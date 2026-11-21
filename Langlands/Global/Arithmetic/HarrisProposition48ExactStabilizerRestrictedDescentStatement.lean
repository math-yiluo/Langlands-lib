import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerReductionStatement
import Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeSupercuspidalStatement

/-!
# The singleton branch and the reduction under condition (4.12) with restricted supercuspidal descent

The singleton branch of the induction for Harris (1998), Proposition 4.8, under
condition (4.12), and the explicit-input reduction of the exact-stabilizer
proposition, with the restricted supercuspidal descent along cyclic base change
(B5r) in place of B5. B5r assumes, besides the hypotheses of B5, that the base
change is also supercuspidal at the unique place above a second finite place.
The singleton branch has this at the place conjugate to the auxiliary place.
The published forms with B5 are unchanged. The totally complex forms use the
totally complex form of B5r. Proposition definitions only.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.GaloisRepresentation LocalFactor.CommonClosure

/-- `Proposition48ExactStabilizerSingletonBranchStatement` with the restricted
supercuspidal descent `RestrictedCyclicWeakBaseChangeSupercuspidalStatement`
(B5r) in place of `CyclicWeakBaseChangeSupercuspidalStatement` (B5). Every other
premise and the body are unchanged. -/
def Proposition48ExactStabilizerRestrictedSingletonBranchStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicStableDescentStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- The totally complex form of
`Proposition48ExactStabilizerRestrictedSingletonBranchStatement`: the premises
of `Proposition48ExactStabilizerSingletonBranchTCStatement`, with
`RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement` in place of
`CyclicWeakBaseChangeSupercuspidalTCStatement`; the body is unchanged. -/
def Proposition48ExactStabilizerRestrictedSingletonBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) →
      Q.HasParameterSolution.{uF, uV}

/-- `Proposition48ExactStabilizerReductionStatement` with the restricted singleton
branch in place of the singleton branch and B5r in place of B5. The other twenty
inputs and the conclusion are unchanged. -/
def Proposition48ExactStabilizerRestrictedReductionStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessStatement.{uF, uV} ∧
    Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV} ∧
    Proposition48ExactStabilizerRestrictedSingletonBranchStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceStatement.{uV} ∧
    CyclicRegularInductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}

/-- The totally complex form of
`Proposition48ExactStabilizerRestrictedReductionStatement`:
`Proposition48ExactStabilizerReductionTCStatement` with the restricted singleton
branch TC form in place of the singleton branch TC form and the TC form of B5r
in place of the TC form of B5. -/
def Proposition48ExactStabilizerRestrictedReductionTCStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerPrimeBranchTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerRestrictedSingletonBranchTCStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityTCStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceTCStatement.{uV} ∧
    CyclicRegularInductionTCStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}

end Langlands.Global.Harris
