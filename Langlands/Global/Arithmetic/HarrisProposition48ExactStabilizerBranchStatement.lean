import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement
import Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceStatement
import Langlands.Automorphic.CuspidalComplexParameterBridgeStatement

/-!
# The two branches of Harris's Proposition 4.8 under the exact-stabilizer condition

The prime-orbit and singleton branches of the induction for Harris (1998),
Proposition 4.8, when the auxiliary character satisfies condition (4.12)
instead of general position. The children are supplied with exact-stabilizer
validity and with the complex-place parameters of the induced representation,
and the branch produces a solution with these parameters. The prime branch no
longer assumes the local comparison at a split supercuspidal place; it assumes
instead that the Mackey components of the step are distinct
(`HasDistinctMackeyComponents`). Both branches assume the restricted
complex-place compatibility of cyclic base change and the archimedean bridge.
The totally complex forms replace the global inputs by their totally complex
forms. Proposition definitions only.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.GaloisRepresentation LocalFactor.CommonClosure

/-- The prime-orbit branch under condition (4.12). From Harris's Theorem 1.2,
rigidity, isobaric invariance, the three cyclic inputs of the published prime
branch, the restricted complex-place compatibility and the archimedean bridge:
a problem with exact-stabilizer validity and a prime cyclic step `D` with
`[D : E]` Mackey classes and distinct Mackey components has a solution with the
induced complex-place parameters, once every child has an untwisted solution
`S` with the induced complex-place parameters of the child. -/
def Proposition48ExactStabilizerPrimeBranchStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicRegularInductionStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      Q.HasDistinctMackeyComponents.{uF, uV} D →
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

/-- The singleton branch under condition (4.12). From Harris's Theorem 1.2,
rigidity, isobaric invariance, stable cyclic descent, supercuspidal descent
along cyclic base change, the restricted complex-place compatibility and the
archimedean bridge: a problem with exact-stabilizer validity and a prime cyclic
step `D` with one Mackey class has a solution with the induced complex-place
parameters, once every child has an untwisted solution `S` with the induced
complex-place parameters of the child. -/
def Proposition48ExactStabilizerSingletonBranchStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicStableDescentStatement.{0, 0, uV, uV} →
  CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} →
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

/-- The totally complex form of `Proposition48ExactStabilizerPrimeBranchStatement`:
rigidity, isobaric invariance and the three cyclic inputs are replaced by their
totally complex forms; Theorem 1.2, the restricted complex-place compatibility,
the bridge and the body are unchanged. -/
def Proposition48ExactStabilizerPrimeBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicRegularInductionTCStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} →
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} →
  CuspidalComplexParameterBridgeTCStatement.{0} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      Q.HasDistinctMackeyComponents.{uF, uV} D →
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

/-- The totally complex form of `Proposition48ExactStabilizerSingletonBranchStatement`:
rigidity, isobaric invariance, stable cyclic descent and supercuspidal descent
are replaced by their totally complex forms; Theorem 1.2, the restricted
complex-place compatibility, the bridge and the body are unchanged. -/
def Proposition48ExactStabilizerSingletonBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
  CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} →
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

end Langlands.Global.Harris
