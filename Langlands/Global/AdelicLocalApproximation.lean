import Langlands.Global.AdelicCoordinateInclusions
import Langlands.Global.AdelicCompactRepresentatives
import Langlands.Global.CocompactLocalApproximation
import Mathlib.Topology.Algebra.Field

/-! # Approximation away from a single actual adelic coordinate -/

noncomputable section

open Set Filter Topology
open scoped RestrictedProduct

universe u

namespace Langlands.Global
namespace AdelicLocalApproximation

open HeckeFunctionalEquation

variable (K : Type u) [Field K] [NumberField K]

local instance : DecidableEq (FinitePlace K) := Classical.decEq _
local instance : DecidableEq (InfinitePlace K) := Classical.decEq _

@[simp]
theorem finiteProjection_finiteAdditiveInclusion (v : FinitePlace K) (x : FiniteCompletion K v) :
    finiteProjection K v (finiteAdditiveInclusion K v x) = x := by
  change Pi.single v x v = x
  simp

@[simp]
theorem infiniteProjection_infiniteAdditiveInclusion (v : InfinitePlace K) (x : InfiniteCompletion K v) :
    infiniteProjection K v (infiniteAdditiveInclusion K v x) = x := by
  change Pi.single v x v = x
  simp

@[simp]
theorem mul_finiteAdditiveInclusion (a : Adeles K) (v : FinitePlace K) (x : FiniteCompletion K v) :
    a * finiteAdditiveInclusion K v x = finiteAdditiveInclusion K v (a.2 v * x) := by
  apply Prod.ext
  · change a.1 * 0 = 0
    simp
  · apply RestrictedProduct.ext
    intro w
    change a.2 w * Pi.single v x w = Pi.single v (a.2 v * x) w
    by_cases hw : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hw]

@[simp]
theorem mul_infiniteAdditiveInclusion (a : Adeles K) (v : InfinitePlace K) (x : InfiniteCompletion K v) :
    a * infiniteAdditiveInclusion K v x = infiniteAdditiveInclusion K v (a.1 v * x) := by
  apply Prod.ext
  · funext w
    change a.1 w * Pi.single v x w = Pi.single v (a.1 v * x) w
    by_cases hw : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hw]
  · change a.2 * 0 = 0
    simp

private theorem not_isCompact_field_univ
    (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [T2Space F] [Infinite F] : ¬ IsCompact (univ : Set F) := by
  intro h
  let : CompactSpace F := isCompact_univ_iff.mp h
  let : Finite F := DivisionRing.finite_of_compactSpace_of_t2Space
  exact not_finite F

/-- Every neighborhood contains a nonzero diagonal element after deleting one finite coordinate. -/
theorem finite_small (v : FinitePlace K) (N : Set (Adeles K)) (hN : N ∈ 𝓝 0) :
    ∃ k : K, k ≠ 0 ∧ diagonal K k * (1 - finiteAdditiveInclusion K v 1) ∈ N := by
  let : Infinite (FiniteCompletion K v) :=
    Infinite.of_injective (algebraMap K (FiniteCompletion K v)) (algebraMap K _).injective
  obtain ⟨C, hC, hcover⟩ := exists_compact_sub_diagonal_mem K
  apply exists_ne_zero_mul_mem_of_compact_section
    (diagonal K).toAddMonoidHom (finiteProjection K v).toAddMonoidHom
    (continuous_finiteProjection K v) (finiteAdditiveInclusion K v)
    (finiteProjection_finiteAdditiveInclusion K v)
    (not_isCompact_field_univ (FiniteCompletion K v))
    (1 - finiteAdditiveInclusion K v 1) ?_ C hC hcover N hN
  intro x
  rw [mul_sub, mul_one, mul_finiteAdditiveInclusion]
  change finiteAdditiveInclusion K v x - finiteAdditiveInclusion K v (finiteProjection K v (finiteAdditiveInclusion K v x) * 1) = 0
  simp

/-- Every neighborhood contains a nonzero diagonal element after deleting one infinite coordinate. -/
theorem infinite_small (v : InfinitePlace K) (N : Set (Adeles K)) (hN : N ∈ 𝓝 0) :
    ∃ k : K, k ≠ 0 ∧ diagonal K k * (1 - infiniteAdditiveInclusion K v 1) ∈ N := by
  let : Infinite (InfiniteCompletion K v) :=
    Infinite.of_injective (algebraMap K (InfiniteCompletion K v)) (algebraMap K _).injective
  obtain ⟨C, hC, hcover⟩ := exists_compact_sub_diagonal_mem K
  apply exists_ne_zero_mul_mem_of_compact_section
    (diagonal K).toAddMonoidHom (infiniteProjection K v).toAddMonoidHom
    (continuous_infiniteProjection K v) (infiniteAdditiveInclusion K v)
    (infiniteProjection_infiniteAdditiveInclusion K v)
    (not_isCompact_field_univ (InfiniteCompletion K v))
    (1 - infiniteAdditiveInclusion K v 1) ?_ C hC hcover N hN
  intro x
  rw [mul_sub, mul_one, mul_infiniteAdditiveInclusion]
  change infiniteAdditiveInclusion K v x - infiniteAdditiveInclusion K v (infiniteProjection K v (infiniteAdditiveInclusion K v x) * 1) = 0
  simp

/-- A nonzero actual adele generates a one-place idempotent ideal, whose complementary
projection has arbitrarily small nonzero diagonal field elements. -/
theorem exists_local_factor (a : Adeles K) (ha : a ≠ 0) :
    ∃ e z : Adeles K, e = a * z ∧
      ∀ N ∈ 𝓝 (0 : Adeles K), ∃ k : K, k ≠ 0 ∧ diagonal K k * (1 - e) ∈ N := by
  classical
  by_cases hf : ∃ v : FinitePlace K, a.2 v ≠ 0
  · obtain ⟨v, hv⟩ := hf
    refine ⟨finiteAdditiveInclusion K v 1, finiteAdditiveInclusion K v (a.2 v)⁻¹, ?_, finite_small K v⟩
    rw [mul_finiteAdditiveInclusion, mul_inv_cancel₀ hv]
  · have hi : ∃ v : InfinitePlace K, a.1 v ≠ 0 := by
      by_contra! h
      apply ha
      apply Prod.ext
      · funext v
        exact h v
      · apply RestrictedProduct.ext
        intro v
        exact not_ne_iff.mp (not_exists.mp hf v)
    obtain ⟨v, hv⟩ := hi
    refine ⟨infiniteAdditiveInclusion K v 1, infiniteAdditiveInclusion K v (a.1 v)⁻¹, ?_, infinite_small K v⟩
    rw [mul_infiniteAdditiveInclusion, mul_inv_cancel₀ hv]

end AdelicLocalApproximation
end Langlands.Global
