import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # A nonzero adjoint eigenvalue for an adjoint-nilpotent element -/

universe u v

namespace Langlands

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- If `ad e` is nilpotent in a finite-dimensional Lie algebra with
nondegenerate Killing form, then `e` is an eigenvector of some `ad h`
with eigenvalue one. -/
theorem exists_lie_eq_of_isNilpotent_ad {k : Type u} [Field k] {L : Type v}
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] [LieAlgebra.IsKilling k L]
    (e : L) (he : IsNilpotent (LieAlgebra.ad k L e)) : ∃ h : L, ⁅h, e⁆ = e := by
  let A := LieAlgebra.ad k L e
  let B := killingForm k L
  have hB : B.Nondegenerate := IsKilling.killingForm_nondegenerate k L
  have hle : A.range ≤ B.orthogonal A.ker := by
    rintro _ ⟨x, rfl⟩
    intro y hy
    have hxy : ⁅e, y⁆ = 0 := hy
    have hye : ⁅y, e⁆ = 0 := by rw [← lie_skew y e, hxy, neg_zero]
    change B y ⁅e, x⁆ = 0
    rw [← LieModule.traceForm_apply_lie_apply k L L, hye, map_zero, LinearMap.zero_apply]
  have heq : A.range = B.orthogonal A.ker := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [LinearMap.BilinForm.finrank_orthogonal hB]
    exact Nat.sub_le_of_le_add A.finrank_range_add_finrank_ker.ge
  have hor : e ∈ B.orthogonal A.ker := by
    intro y hy
    have hey : ⁅e, y⁆ = 0 := hy
    have hye : ⁅y, e⁆ = 0 := by rw [← lie_skew y e, hey, neg_zero]
    have hc : Commute (LieAlgebra.ad k L y) A := by
      apply sub_eq_zero.mp
      rw [← Ring.lie_def, ← (LieAlgebra.ad k L).map_lie, hye, map_zero]
    change killingForm k L y e = 0
    rw [killingForm_apply_apply, ← Module.End.mul_eq_comp]
    exact isNilpotent_iff_eq_zero.mp
      (LinearMap.isNilpotent_trace_of_isNilpotent (hc.isNilpotent_mul_left he))
  rw [← heq] at hor
  obtain ⟨x, hx⟩ := hor
  refine ⟨-x, ?_⟩
  have h : ⁅e, x⁆ = e := hx
  rw [neg_lie, lie_skew e x, h]

end Langlands
