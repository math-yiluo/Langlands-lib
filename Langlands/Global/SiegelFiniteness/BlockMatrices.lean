import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Block-triangular matrices

Elementary matrix facts used for Siegel finiteness:

* a square matrix whose rows `t ≥ i` vanish in the columns `j ≤ i` is singular, so every
  invertible matrix has a nonzero entry `(t, j)` with `j ≤ i ≤ t`;
* the matrices that vanish in the lower-left block (rows `≥ s`, columns `< s`) are closed under
  multiplication and contain the upper triangular matrices;
* a unitary matrix that vanishes in the lower-left block also vanishes in the upper-right block.
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Global.SiegelFiniteness

variable {n : ℕ}

section Det

variable {R : Type*} [CommRing R]

/-- **Pigeonhole for determinants.** -/
theorem det_eq_zero_of_lowerLeft (M : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (h : ∀ t j : Fin n, i ≤ t → j ≤ i → M t j = 0) : M.det = 0 := by
  classical
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  -- some column `c ≤ i` is sent to a row `σ c ≥ i`
  obtain ⟨c, hc, hσc⟩ : ∃ c : Fin n, c ≤ i ∧ i ≤ σ c := by
    by_contra hcon
    push Not at hcon
    have hinj : Set.InjOn σ (Finset.Iic i : Set (Fin n)) := fun a _ b _ hab => σ.injective hab
    have hmaps : ∀ c ∈ Finset.Iic i, σ c ∈ Finset.Iio i := fun c hc =>
      Finset.mem_Iio.mpr (hcon c (Finset.mem_Iic.mp hc))
    have hcard := Finset.card_le_card_of_injOn σ hmaps hinj
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  have hzero : ∏ k, M (σ k) k = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ c) (h _ _ hσc hc)
  rw [hzero, smul_zero]

/-- Every invertible matrix has a nonzero entry `(t, j)` with `j ≤ i ≤ t`. -/
theorem exists_lowerLeft_ne_zero {K : Type*} [Field K] (γ : Matrix.GeneralLinearGroup (Fin n) K)
    (i : Fin n) : ∃ t j : Fin n, i ≤ t ∧ j ≤ i ∧ γ.val t j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdet := det_eq_zero_of_lowerLeft γ.val i hcon
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp γ.isUnit).ne_zero hdet

end Det

section Block

variable {R : Type*} [CommRing R]

/-- `M` vanishes in the lower-left block: rows `≥ s`, columns `< s`. -/
def IsBlockUpper (s : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, s ≤ i.val → j.val < s → M i j = 0

theorem isBlockUpper_of_isUpperTriangular {M : Matrix (Fin n) (Fin n) R}
    (hM : M.IsUpperTriangular) (s : ℕ) : IsBlockUpper s M :=
  fun i j hi hj => hM (show j < i from Fin.lt_def.mpr (by omega))

theorem IsBlockUpper.mul {s : ℕ} {M N : Matrix (Fin n) (Fin n) R} (hM : IsBlockUpper s M)
    (hN : IsBlockUpper s N) : IsBlockUpper s (M * N) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k.val < s
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j (by omega) hj, mul_zero]

end Block

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜]

theorem unitary_row_sum {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    (a : Fin n) : ∑ b, ‖U a b‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h' : ((∑ b, ‖U a b‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.star_apply, RCLike.star_def, RCLike.mul_conj]
  exact_mod_cast h'

theorem unitary_col_sum {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜)
    (b : Fin n) : ∑ a, ‖U a b‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) b) b
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h' : ((∑ a, ‖U a b‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.star_apply, RCLike.star_def, mul_comm, RCLike.mul_conj]
  exact_mod_cast h'

/-- **A unitary matrix vanishing in the lower-left block vanishes in the upper-right block.** -/
theorem unitary_upperRight_eq_zero {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) {s : ℕ} (hblock : IsBlockUpper s U)
    (a b : Fin n) (ha : a.val < s) (hb : s ≤ b.val) : U a b = 0 := by
  classical
  set lo : Finset (Fin n) := Finset.univ.filter fun i => i.val < s with hlo
  -- rows in `lo` have total mass `#lo`
  have hrows : ∑ i ∈ lo, ∑ j, ‖U i j‖ ^ 2 = lo.card := by
    rw [Finset.sum_congr rfl fun i _ => unitary_row_sum hU i]
    simp
  -- columns in `lo` have total mass `#lo`, all of it in the rows of `lo`
  have hcols : ∑ j ∈ lo, ∑ i ∈ lo, ‖U i j‖ ^ 2 = lo.card := by
    have : ∀ j ∈ lo, ∑ i ∈ lo, ‖U i j‖ ^ 2 = 1 := by
      intro j hj
      rw [← unitary_col_sum hU j]
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      have hi' : s ≤ i.val := by
        simp only [hlo, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        exact hi
      have hj' : j.val < s := by
        simp only [hlo, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj
      rw [hblock i j hi' hj', norm_zero]
      ring
    rw [Finset.sum_congr rfl this]
    simp
  -- hence the mass of the upper-right block is zero
  have hsplit : ∀ i, ∑ j, ‖U i j‖ ^ 2 =
      ∑ j ∈ lo, ‖U i j‖ ^ 2 + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < s),
        ‖U i j‖ ^ 2 := by
    intro i
    rw [hlo, Finset.sum_filter_add_sum_filter_not]
  have hzero : ∑ i ∈ lo, ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < s),
      ‖U i j‖ ^ 2 = 0 := by
    have h1 : ∑ i ∈ lo, ∑ j, ‖U i j‖ ^ 2 = ∑ i ∈ lo, ∑ j ∈ lo, ‖U i j‖ ^ 2 +
        ∑ i ∈ lo, ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < s), ‖U i j‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hsplit i
    rw [Finset.sum_comm] at hcols
    linarith
  have hnonneg : ∀ i ∈ lo, 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < s),
      ‖U i j‖ ^ 2 := fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have ha' : a ∈ lo := by simp [hlo, ha]
  have hb' : b ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < s) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact hb
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero a ha'
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖U a j‖).mp hrow b hb'
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hentry)

end Unitary

end Langlands.Global.SiegelFiniteness
