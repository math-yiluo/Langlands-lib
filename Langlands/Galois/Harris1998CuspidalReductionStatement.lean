import Langlands.Galois.HarrisEvenGeometricStatement
import Langlands.Galois.HarrisOddNormalizedExistenceStatement
import Langlands.Galois.HarrisRankOneStatement

/-! # Reduction of Harris 1998, Theorem 1.2 in the cuspidal case -/

noncomputable section

universe uE uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Global

/-- The named rank-one, geometric, local, and quadratic inputs imply the
published cuspidal statement of Harris's Theorem 1.2. -/
def Harris1998Theorem12CuspidalReductionStatement : Prop :=
  HarrisRankOneHeckeSpectrumStatement.{uE, uW} →
  AlgebraicUnitaryHeckeCharacterRealizationStatement.{uE, uL} →
  HarrisEvenGeometricPowerStatement.{uE, uL, uV, uW} →
  TaylorLabelledMultiplicityRemovalStatement.{uE, uL, uV} →
  RegularHodgeTateCoefficientDescentStatement.{uE, uL, uV} →
  HarrisEvenMultiplicityReductionStatement.{uE, uL, uV, uW} →
  Harris.HarrisParityAuxiliaryFieldsStatement.{uE} →
  Harris.ConjugateSelfDualUnitaryCentralCharacterStatement.{uE} →
  CyclicPrimeIsobaricBaseChangeTCStatement.{uE, uE, uW, uW} →
  QuadraticWeakBaseChangeSplitSquareIntegrableStatement.{uE, uE, uW, uW} →
  CyclicWeakBaseChangeComplexPlaceTCStatement.{uE, uE, uW, uW} →
  CuspidalComplexParameterBridgeTCStatement.{uE} →
  HarrisParityBaseChangeStatement.{uE, uW} →
  QuadraticPatchingStatement.{uE, uL, uV} →
  QuadraticFrobeniusPatchingStatement.{uE, uL, uV} →
  AbsoluteGeometricFrobeniusDensityStatement.{uE} →
  FiniteCoefficientModelStatement.{uE, uL, uV} →
  HarrisOddNormalizedExistenceReductionStatement.{uE, uL, uV, uW} →
  Harris1998Theorem12CuspidalStatement.{uE, uL, uV, uW}

end Langlands.GaloisRepresentation
