import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # The inverse-adjoint action of a Hilbert representation -/

noncomputable section

open scoped InnerProduct InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

variable {G : Type*} [Group G] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : G →* (H →L[ℂ] H))

/-- The inverse-adjoint action on a complex Hilbert space. The conjugate-linear Riesz
map identifies this model with the complex continuous dual action. -/
def hilbertContragredient : G →* (H →L[ℂ] H) where
  toFun g := star (R g⁻¹)
  map_one' := by rw [inv_one, map_one, star_one]
  map_mul' g h := by rw [mul_inv_rev, map_mul, star_mul]

@[simp]
theorem hilbertContragredient_apply (g : G) : hilbertContragredient R g = (R g⁻¹)† :=
  rfl

/-- Evaluation of the Riesz functional of an adjoint translate is inverse precomposition. -/
theorem inner_hilbertContragredient (g : G) (u v : H) :
    ⟪hilbertContragredient R g u, v⟫_ℂ = ⟪u, R g⁻¹ v⟫_ℂ :=
  (R g⁻¹).adjoint_inner_left v u

@[simp]
theorem norm_hilbertContragredient (g : G) : ‖hilbertContragredient R g‖ = ‖R g⁻¹‖ :=
  ContinuousLinearMap.adjoint.norm_map _

@[simp]
theorem hilbertContragredient_hilbertContragredient :
    hilbertContragredient (hilbertContragredient R) = R := by
  ext g v
  simp

/-- Closed invariant subspaces for the inverse-adjoint action have invariant orthogonal
complements for the original action. -/
theorem isTopologicallyIrreducible_hilbertContragredient
    (hR : IsTopologicallyIrreducible R) : IsTopologicallyIrreducible (hilbertContragredient R) := by
  refine ⟨hR.1, fun W hW hstable => ?_⟩
  have hWo (g : G) (v : H) (hv : v ∈ Wᗮ) : R g v ∈ Wᗮ := by
    apply (W.mem_orthogonal _).mpr
    intro u hu
    have hgu : hilbertContragredient R g⁻¹ u ∈ W := hstable g⁻¹ u hu
    simpa only [inner_hilbertContragredient, inv_inv] using (W.mem_orthogonal _).mp hv _ hgu
  obtain h | h := hR.2 Wᗮ W.isClosed_orthogonal hWo
  · right
    rw [← hW.submodule_topologicalClosure_eq, ← W.orthogonal_orthogonal_eq_closure,
      h, Submodule.bot_orthogonal_eq_top]
  · left
    rw [← hW.submodule_topologicalClosure_eq, ← W.orthogonal_orthogonal_eq_closure,
      h, Submodule.top_orthogonal_eq_bot]

end Langlands.Archimedean
