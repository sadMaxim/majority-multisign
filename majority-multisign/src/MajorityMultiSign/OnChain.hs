{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module MajorityMultiSign.OnChain (
  findUTxO,
  validator,
  validatorAddress,
  validatorFromIdentifier,
  validatorHash,
) where

import Cardano.Prelude (rightToMaybe)
import Data.Kind (Type)
import Data.List.Extra (firstJust)
import Data.Map qualified as Map
import Data.Row (Row)
import Data.Text (Text)
import Ledger (Address, ChainIndexTxOut (..), Datum (..), PubKeyHash, ScriptContext (..), scriptHashAddress, txSignedBy)
import Ledger qualified
import Ledger.Scripts qualified as Scripts
import Ledger.Typed.Scripts qualified as TypedScripts
import MajorityMultiSign.Schema (
  MajorityMultiSign,
  MajorityMultiSignDatum (..),
  MajorityMultiSignIdentifier (..),
  MajorityMultiSignRedeemer (..),
  MajorityMultiSignValidatorParams (..),
 )
import Plutus.Contract (
  Contract,
  ContractError (..),
  throwError,
  utxosAt,
 )
import Plutus.V1.Ledger.Api (TxOut (..), TxOutRef, fromBuiltinData)
import Plutus.V1.Ledger.Contexts (findDatumHash)
import Plutus.V1.Ledger.Value (assetClassValueOf)
import PlutusTx qualified
import PlutusTx.Builtins (divideInteger, greaterThanEqualsInteger)
import PlutusTx.Prelude hiding (take)

{-# INLINEABLE mkValidator #-}
mkValidator ::
  MajorityMultiSignValidatorParams ->
  MajorityMultiSignDatum ->
  MajorityMultiSignRedeemer ->
  ScriptContext ->
  Bool
mkValidator params dat red ctx =
  hasCorrectToken params ctx (getExpectedDatum red dat)
    && isSufficientlySigned red dat ctx

removeSigners :: [PubKeyHash] -> [PubKeyHash] -> [PubKeyHash]
removeSigners [] _ = []
removeSigners xs [] = xs -- Not strictly needed, but more efficient
removeSigners (x : xs) ys = if x `elem` ys then removeSigners xs ys else x : removeSigners xs ys

-- | Calculates the expected output datum from the current datum and the redeemer
{-# INLINEABLE getExpectedDatum #-}
getExpectedDatum :: MajorityMultiSignRedeemer -> MajorityMultiSignDatum -> MajorityMultiSignDatum
getExpectedDatum UseSignaturesAct datum = datum
getExpectedDatum UpdateKeysAct {..} datum = datum {signers = keys}

-- | Checks if, when setting new signatures, all new keys have signed the transaction
hasNewSignatures :: MajorityMultiSignRedeemer -> MajorityMultiSignDatum -> ScriptContext -> Bool
hasNewSignatures UseSignaturesAct _ _ = True
hasNewSignatures UpdateKeysAct {..} MajorityMultiSignDatum {..} ctx = all (txSignedBy $ scriptContextTxInfo ctx) $ keys `removeSigners` signers

-- | Checks the script has the correct token (containing the asset we want), forwards it to the right place, and has the datum we expect
{-# INLINEABLE hasCorrectToken #-}
hasCorrectToken :: MajorityMultiSignValidatorParams -> ScriptContext -> MajorityMultiSignDatum -> Bool
hasCorrectToken MajorityMultiSignValidatorParams {..} ctx expectedDatum =
  isJust assetTxOut
    && (assetTxOut >>= txOutDatumHash) == findDatumHash (Datum $ PlutusTx.toBuiltinData expectedDatum) (scriptContextTxInfo ctx)
  where
    continuing :: [TxOut]
    continuing = Ledger.getContinuingOutputs ctx

    checkAsset :: TxOut -> Maybe TxOut
    checkAsset txOut = if assetClassValueOf (txOutValue txOut) asset > 0 then Just txOut else Nothing

    assetTxOut :: Maybe TxOut
    assetTxOut = firstJust checkAsset continuing

-- | Checks the validator is signed by more than half of the signers on the datum
{-# INLINEABLE isSufficientlySigned #-}
isSufficientlySigned :: MajorityMultiSignRedeemer -> MajorityMultiSignDatum -> ScriptContext -> Bool
isSufficientlySigned red dat@MajorityMultiSignDatum {..} ctx =
  length signersPresent `greaterThanEqualsInteger` ((length signers + 1) `divideInteger` 2)
    && hasNewSignatures red dat ctx
  where
    signersPresent :: [PubKeyHash]
    signersPresent = filter (txSignedBy $ scriptContextTxInfo ctx) signers

inst :: MajorityMultiSignValidatorParams -> TypedScripts.TypedValidator MajorityMultiSign
inst params =
  TypedScripts.mkTypedValidator @MajorityMultiSign
    ($$(PlutusTx.compile [||mkValidator||]) `PlutusTx.applyCode` PlutusTx.liftCode params)
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TypedScripts.wrapValidator @MajorityMultiSignDatum @MajorityMultiSignRedeemer

validator :: MajorityMultiSignValidatorParams -> Scripts.Validator
validator = TypedScripts.validatorScript . inst

validatorHash :: MajorityMultiSignValidatorParams -> Scripts.ValidatorHash
validatorHash = TypedScripts.validatorHash . inst

validatorAddress :: MajorityMultiSignValidatorParams -> Address
validatorAddress = Ledger.scriptAddress . validator

-- | Gets the validator from an identifier
validatorFromIdentifier :: MajorityMultiSignIdentifier -> Scripts.Validator
validatorFromIdentifier MajorityMultiSignIdentifier {asset} = validator $ MajorityMultiSignValidatorParams asset

-- | Finds the UTxO in a majority multisign containing the asset, and returns it, its datum and the signer list
findUTxO :: forall (w :: Type) (s :: Row Type). MajorityMultiSignIdentifier -> Contract w s ContractError ((TxOutRef, ChainIndexTxOut), Datum, [PubKeyHash])
findUTxO mms = do
  utxos <- utxosAt $ scriptHashAddress mms.address
  let utxoFiltered = Map.toList $ Map.filter ((> 0) . flip assetClassValueOf mms.asset . txOutValue . Ledger.toTxOut) utxos
  case utxoFiltered of
    [(txOutRef, txOut)] ->
      maybeToError "Couldn't extract datum" $ do
        datum <- getChainIndexTxOutDatum txOut
        typedDatum <- fromBuiltinData @MajorityMultiSignDatum $ getDatum datum
        return ((txOutRef, txOut), datum, typedDatum.signers)
    _ -> throwError $ OtherError "Couldn't find UTxO"

-- | fromJust that gives a Contract error
maybeToError ::
  forall (w :: Type) (s :: Row Type) (a :: Type).
  Text ->
  Maybe a ->
  Contract w s ContractError a
maybeToError err = maybe (throwError $ OtherError err) return

-- | Extracts the datum from a ChainIndexTxOut
getChainIndexTxOutDatum :: ChainIndexTxOut -> Maybe Datum
getChainIndexTxOutDatum PublicKeyChainIndexTxOut {} = Nothing
getChainIndexTxOutDatum ScriptChainIndexTxOut {_ciTxOutDatum = eDatum} = rightToMaybe eDatum
