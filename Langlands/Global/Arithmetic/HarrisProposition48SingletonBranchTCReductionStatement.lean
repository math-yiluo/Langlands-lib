import Langlands.Automorphic.CuspidalArithmeticTransportStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeRegularAlgebraicStatement
import Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeSupercuspidalStatement
import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Global.Arithmetic.HarrisCyclicDescentCorrectionStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExtensionMatchingStatement
import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement
import Langlands.Global.Arithmetic.HarrisProposition48SingletonDescentStatement

/-! # Named-input reduction of the totally complex Harris singleton branch -/

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.FiniteRepresentation Langlands.GaloisRepresentation

/-- The child transport, local and archimedean descent, finite correction, and
Galois extension matching inputs imply the unchanged TC singleton target. -/
def Proposition48SingletonBranchTCReductionStatement : Prop :=
  Proposition48SingletonChildNormalizationStatement.{uF, uV} →
  Proposition48MackeyChildTransportStatement.{uF, uV} →
  ArithmeticComapRegularAlgebraicStatement.{0, 0} →
  ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV} →
  ArithmeticComapConjugateSelfDualStatement.{0, 0} →
  Proposition48SingletonMackeyGaloisStableTCStatement.{uF, uV} →
  ConjugateSelfDualUnitaryCentralCharacterStatement.{0} →
  ConjugateSelfDualSupercuspidalConjPlaceStatement.{0, uV} →
  SplitPlaceNeConjPlaceStatement.{0} →
  Proposition48AuxiliaryStepPlacesStatement.{uF} →
  WeakBaseChangeUnitaryCentralCharacterStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
  CyclicWeakBaseChangeRegularAlgebraicTCStatement.{0, 0, uV, uV} →
  Proposition48AuxiliaryTheorem12FieldStatement.{uF} →
  WeakBaseChangeConjugateDualDescentStatement.{0, 0, uV, uV} →
  CMNormKernelRealFactorStatement.{0, 0} →
  CMFiniteRealCharacterExtensionStatement.{0} →
  FiniteCharacterConjugateDualCorrectionStatement.{0, uV} →
  AlgebraicHeckeLambdaAdicRealizationStatement.{0, 0} →
  FiniteOrderWeakAssociationUntwistStatement.{0, 0, uV, uV} →
  HeckeCharacterGaloisInductionStatement.{0, 0, 0} →
  Proposition48SingletonMonomialRestrictionStatement.{uF} →
  PureFrobeniusWeightAlignmentStatement.{0, 0, uV} →
  CyclicExtensionTwistClassificationStatement.{0, 0, uV, 0} →
  Proposition48SingletonExtensionMatchingTCStatement.{uF, uV} →
  WeakInductionConjugateInverseSelfDualTCStatement.{uV, 0, 0} →
  Proposition48SingletonBranchTCStatement.{uF, uV}

end Langlands.Global.Harris
