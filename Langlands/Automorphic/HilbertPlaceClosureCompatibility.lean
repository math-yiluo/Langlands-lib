import Langlands.Automorphic.HilbertCoefficientPlaceClosure
import Langlands.Automorphic.CuspidalArchimedeanPlaceComponent
import Langlands.Automorphic.CuspidalHilbertIntertwinerCore
import Langlands.Global.ArchimedeanPlaceRestriction

/-! # Place closure compatibility on a supplied form completion -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Matrix.Norms.Operator TensorProduct

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL HilbertCoefficientComparison RankinSelbergGlobal
universe u uV uX uG uK uL
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Agreement on embedded compact vectors and invariance of the closed images
of algebraic subspaces stable under the compact and Lie actions. -/
def PlaceClosureCompatibility {G : Type uG} [Monoid G] {K : Type uK} [Group K]
    {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E) (iK : K → G)
    (κ : Representation ℂ K V) (d : L →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  (∀ k v, π (iK k) (j v) = j (κ k v)) ∧
    ∀ W : Submodule ℂ V, PlaceComponent.IsStable κ d W → PreservesImageClosure π j W

namespace OperatorUnitaryFormCore.AdelicCompletion

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- If a point of a local group is the included global compact point, the
restricted operator there is the completed compact operator. -/
theorem placeAction_apply_of_compact {G : Type uG} [Monoid G]
    (ι : G →* ArchimedeanGL F n) (g : G) (k : standardInfiniteCompact F n)
    (hk : ι g = archimedeanGLCoordinates F n k.val) (x : b.HilbertCompletion) :
    placeAction B.action ι g x = b.completedCompactOperator k x := by
  change B.action (AdelicGL.ofInfinite F n
    ((archimedeanGLCoordinates F n).symm (ι g))) x = _
  have h := (congrArg (archimedeanGLCoordinates F n).symm hk).trans
    ((archimedeanGLCoordinates F n).symm_apply_apply k.val)
  exact (congrArg (fun a : InfiniteAdelicGL F n => B.action (AdelicGL.ofInfinite F n a) x) h).trans
    (B.boundedCompatibility.2 k x)

/-- On a supplied completion with the real-place generator comparison, the
actual real-place action takes place-stable closures into themselves. -/
theorem realPlaceClosureCompatibility (w : RP)
    (d : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hd : ∀ Y : RM, ∀ v,
      B.differential (envelopingGenerator F n (complexify F n (realPlaceLieInclusion F n w Y))) v =
        d (1 ⊗ₜ[ℝ] Y) v) :
    PlaceClosureCompatibility (placeAction B.action (realPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ →* RMˣ)
      (κ.comp (realPlaceCompactInclusion F n w).toMonoidHom) d := by
  have hK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : V) :
      placeAction B.action (realPlaceGL F n w) (Unitary.toUnits k) (b.toHilbert v) =
        b.toHilbert (κ (realPlaceCompactInclusion F n w k) v) :=
    (B.placeAction_apply_of_compact (realPlaceGL F n w) (Unitary.toUnits k)
      (realPlaceCompactInclusion F n w k) (ArchimedeanGL.realPlaceGL_unitary w k) _).trans
      (b.completedCompactOperator_toHilbert _ v)
  refine ⟨hK, fun W hW => ?_⟩
  refine preservesImageClosure_of_coefficients B.action b.toHilbert W B.differential
    B.coefficients (realPlaceGL F n w) (realPlaceMatrix w) (realPlaceLieInclusion F n w)
    (fun g => (realPlaceGL_val w g).symm)
    (fun f => analyticAt_realPlaceRestriction w (coordinateExtension F n f))
    (fderiv_realPlaceRestriction w) ?_ (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ →* RMˣ)
    (exists_unitary_point_mem_connectedComponent (𝕜 := ℝ) (m := Fin n)) ?_
  · intro Y v hv
    rw [hd]
    exact hW.2 _ v hv
  · intro k v
    exact ⟨⟨κ (realPlaceCompactInclusion F n w k) v, hW.1 k v v.property⟩, hK k v⟩

/-- The corresponding comparison for the entire real Lie algebra of the
complex-place group. -/
theorem complexPlaceClosureCompatibility (w : CP)
    (d : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hd : ∀ Y : CM, ∀ v,
      B.differential (envelopingGenerator F n (complexify F n (complexPlaceLieInclusion F n w Y))) v =
        d (1 ⊗ₜ[ℝ] Y) v) :
    PlaceClosureCompatibility (placeAction B.action (complexPlaceGL F n w)) b.toHilbert
      (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* CMˣ)
      (κ.comp (complexPlaceCompactInclusion F n w).toMonoidHom) d := by
  have hK (k : Matrix.unitaryGroup (Fin n) ℂ) (v : V) :
      placeAction B.action (complexPlaceGL F n w) (Unitary.toUnits k) (b.toHilbert v) =
        b.toHilbert (κ (complexPlaceCompactInclusion F n w k) v) :=
    (B.placeAction_apply_of_compact (complexPlaceGL F n w) (Unitary.toUnits k)
      (complexPlaceCompactInclusion F n w k) (ArchimedeanGL.complexPlaceGL_unitary w k) _).trans
      (b.completedCompactOperator_toHilbert _ v)
  refine ⟨hK, fun W hW => ?_⟩
  refine preservesImageClosure_of_coefficients B.action b.toHilbert W B.differential
    B.coefficients (complexPlaceGL F n w) (complexPlaceMatrix w) (complexPlaceLieInclusion F n w)
    (fun g => (complexPlaceGL_val w g).symm)
    (fun f => analyticAt_complexPlaceRestriction w (coordinateExtension F n f))
    (fderiv_complexPlaceRestriction w) ?_ (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* CMˣ)
    (exists_unitary_point_mem_connectedComponent (𝕜 := ℂ) (m := Fin n)) ?_
  · intro Y v hv
    rw [hd]
    exact hW.2 _ v hv
  · intro k v
    exact ⟨⟨κ (complexPlaceCompactInclusion F n w k) v, hW.1 k v v.property⟩, hK k v⟩

end OperatorUnitaryFormCore.AdelicCompletion
end Langlands.Automorphic
