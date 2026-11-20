import Langlands.Automorphic.HilbertPlaceClosureCompatibility
import Langlands.Automorphic.CuspidalHilbertAdelicCompletion

/-! # Invariance of local Hilbert closures in the actual adelic completion -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator NumberField TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL HilbertCoefficientComparison
open RankinSelbergGlobal

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance placeClosureRationalGroup (m : ℕ) : AddCommGroup (RationalInvariantFunctions F m) :=
  Submodule.addCommGroup _
local instance placeClosureContinuousGroup (m : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F m) := Submodule.addCommGroup _
local instance placeClosureFiniteSmoothGroup (m : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F m) := Submodule.addCommGroup _
local instance placeClosureFormsGroup (m : ℕ) : AddCommGroup (AutomorphicForms F m) :=
  Submodule.addCommGroup _
local instance placeClosureStableGroup (m : ℕ) : AddCommGroup (StableAutomorphicFunctions F m) :=
  Submodule.addCommGroup _
local instance placeClosureSpaceGroup {m : ℕ} (S : OperatorRealization F m) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

namespace OperatorRealization

variable {S : OperatorRealization F n} {b : S.UnitaryForm}
  (A : OperatorUnitaryFormCore.AdelicCompletion b)

/-- Real-place closure compatibility for the actual operators on the carrier. -/
theorem realPlaceClosureCompatibility
    (hD : ∀ a v, A.differential a v = S.envelopingAction a v) (w : RP) :
    PlaceClosureCompatibility (placeAction A.action (realPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ →* RMˣ)
      (S.realPlaceCompactRepresentation w) (S.realPlaceLieAction w) := by
  refine A.realPlaceClosureCompatibility w (S.realPlaceLieAction w) fun X v => ?_
  have hX := (realPlaceComplexLieInclusion_tmul F n w 1 X).trans
    (complexify_apply F n (realPlaceLieInclusion F n w X)).symm
  exact (hD _ v).trans
    ((congrArg (fun Z => S.envelopingAction (envelopingGenerator F n Z) v) hX.symm).trans
      (realPlaceLieAction_apply S w (1 ⊗ₜ[ℝ] X) v).symm)

/-- Complex-place closure compatibility for the actual operators on the carrier. -/
theorem complexPlaceClosureCompatibility
    (hD : ∀ a v, A.differential a v = S.envelopingAction a v) (w : CP) :
    PlaceClosureCompatibility (placeAction A.action (complexPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* CMˣ)
      (S.complexPlaceCompactRepresentation w) (S.complexPlaceLieAction w) := by
  refine A.complexPlaceClosureCompatibility w (S.complexPlaceLieAction w) fun X v => ?_
  have hX := (complexPlaceComplexLieInclusion_tmul F n w 1 X).trans
    (complexify_apply F n (complexPlaceLieInclusion F n w X)).symm
  exact (hD _ v).trans
    ((congrArg (fun Z => S.envelopingAction (envelopingGenerator F n Z) v) hX.symm).trans
      (complexPlaceLieAction_apply S w (1 ⊗ₜ[ℝ] X) v).symm)

/-- In the reconstructed determinant-band completion, a place-stable algebraic
subspace has invariant Hilbert closure for the full local general linear group.
The local compact actions also agree on the embedded original vectors. -/
def CuspidalHilbertPlaceClosureStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm) (hb : OperatorDeterminantSlice.ComputesBandInnerProduct T.realization b),
    let A := OperatorDeterminantSlice.adelicCompletion T χ hχ hTχ b hb
    (∀ (w : {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal v}),
      PlaceClosureCompatibility (placeAction A.action (realPlaceGL K (r + 1) w)) b.toHilbert
        (Unitary.toUnits : Matrix.unitaryGroup (Fin (r + 1)) ℝ →* (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)ˣ)
        (T.realization.realPlaceCompactRepresentation w) (T.realization.realPlaceLieAction w)) ∧
    ∀ (w : {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex v}),
      PlaceClosureCompatibility (placeAction A.action (complexPlaceGL K (r + 1) w)) b.toHilbert
        (Unitary.toUnits : Matrix.unitaryGroup (Fin (r + 1)) ℂ →* (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)ˣ)
        (T.realization.complexPlaceCompactRepresentation w) (T.realization.complexPlaceLieAction w)

theorem cuspidalHilbertPlaceClosure : CuspidalHilbertPlaceClosureStatement.{u} := by
  intro K _ _ _ r T χ hχ hTχ b hb
  let A := OperatorDeterminantSlice.adelicCompletion T χ hχ hTχ b hb
  have hD : ∀ a v, A.differential a v = T.realization.envelopingAction a v := fun _ _ => rfl
  exact ⟨realPlaceClosureCompatibility A hD, complexPlaceClosureCompatibility A hD⟩

end OperatorRealization
end Langlands.Automorphic
