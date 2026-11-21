import Langlands.Global.Arithmetic.HarrisProposition48PrimeBranchStatement
import Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement
import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Global.Arithmetic.HarrisProposition48CorrectedChildTransportStatement
import Langlands.Global.Arithmetic.HarrisProposition48MonomialRestrictionStatement
import Langlands.Global.Arithmetic.HarrisProposition48ChildComplexParametersStatement
import Langlands.Global.Arithmetic.HarrisProposition48PrimeLocalDistinctnessStatement
import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Automorphic.CuspidalArithmeticTransportStatement
import Langlands.Automorphic.Unramified.IsobaricSpectralTransportStatement
import Langlands.Automorphic.Unramified.CyclicInductionOrbitBaseChangeStatement

/-! # Reductions of the two general-position prime branches of Proposition 4.8 -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.GaloisRepresentation

/-- The named intermediate results used in both prime-branch reductions.
The complex-place steps use totally complex foundations over the actual CM
base and its finite extensions. -/
def Proposition48PrimeBranchCommonInputs : Prop :=
  Proposition48MackeyFibreStatement.{uF} ∧
  Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV} ∧
  Proposition48MackeyChildTransportStatement.{uF, uV} ∧
  Proposition48CorrectedChildTransportStatement.{uF, uV} ∧
  Proposition48PrimeOrbitBasepointStatement.{uF} ∧
  AlgebraicHeckeAvatarExistenceStatement ∧
  HeckeMonomialCollectionStatement.{uV} ∧
  Proposition48MonomialMackeyRestrictionStatement.{uF, uV} ∧
  FiniteDirectSumWeakAssociationStatement.{uV} ∧
  GaloisRestrictionEulerInvarianceStatement.{uV} ∧
  IsobaricEnumerationSpectralAttachmentStatement.{0, uV} ∧
  IsobaricSpectralConjugationStatement.{0, uV} ∧
  Proposition48PrimeLocalDistinctnessStatement.{uF, uV} ∧
  ArithmeticComapUnitaryCentralCharacterStatement.{0, 0} ∧
  ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV} ∧
  ArithmeticComapConjugateSelfDualStatement.{0, 0} ∧
  ConjugateSelfDualUnitaryCentralCharacterStatement.{0} ∧
  CyclicInductionOrbitBaseChangeStatement.{0, 0, uV, uV} ∧
  Proposition48PrimeInductionStagesStatement.{uF, uV} ∧
  CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} ∧
  CyclicWeakBaseChangeComplexPlaceTCStatement.{0, 0, uV, uV} ∧
  IsobaricHeckeComplexPlaceParameterTCStatement.{0, uV} ∧
  Proposition48AuxiliaryChildComplexParametersStatement.{uF, uV} ∧
  Proposition48PrimeInducedParameterStagesStatement.{uF} ∧
  CuspidalComplexParameterBridgeTCStatement.{0} ∧
  Proposition48InducedParameterRegularAlgebraicStatement.{uF}

/-- Intermediate results and conjugate self-duality from unrestricted rigidity
imply the original exact general-position prime branch. Its seven foundational
premises enter through the published target. -/
def Proposition48PrimeBranchReductionStatement : Prop :=
  Proposition48PrimeBranchCommonInputs.{uF, uV} →
  WeakInductionConjugateInverseSelfDualStatement.{uV, 0, 0} →
    Proposition48PrimeBranchStatement.{uF, uV}

/-- Intermediate results and conjugate self-duality from totally complex
rigidity imply the exact totally complex general-position prime branch. -/
def Proposition48PrimeBranchReductionTCStatement : Prop :=
  Proposition48PrimeBranchCommonInputs.{uF, uV} →
  WeakInductionConjugateInverseSelfDualTCStatement.{uV, 0, 0} →
    Proposition48PrimeBranchTCStatement.{uF, uV}

end Langlands.Global.Harris
