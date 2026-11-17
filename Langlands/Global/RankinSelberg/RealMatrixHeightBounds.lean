import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Global.ArchimedeanCharacterGrowth

/-! # Real matrix-height bounds for arbitrary determinant powers -/

noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPlaceRestriction

variable {n : ℕ}

theorem realMatrixHeight_nonneg (g : Langlands.GeneralLinear n ℝ) :
    0 ≤ realMatrixHeight g :=
  Finset.sum_nonneg fun _i _ => Finset.sum_nonneg fun _j _ =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem realMatrixHeight_inv (g : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight g⁻¹ = realMatrixHeight g := by
  simp only [realMatrixHeight, inv_inv, add_comm]

open scoped Matrix.Norms.Frobenius in
theorem realMatrixHeight_eq_frobenius (g : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight g = ‖g.val‖ ^ 2 + ‖(g⁻¹).val‖ ^ 2 := by
  have hsq (A : Matrix (Fin n) (Fin n) ℝ) :
      ‖A‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def]
    simp only [Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  simp only [realMatrixHeight, Finset.sum_add_distrib, hsq]

open scoped Matrix.Norms.Frobenius in
theorem two_le_realMatrixHeight (hn : 0 < n) (g : Langlands.GeneralLinear n ℝ) :
    2 ≤ realMatrixHeight g := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hab : 1 ≤ ‖g.val‖ * ‖(g⁻¹).val‖ := calc
    1 ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := one_le_norm_one _
    _ = ‖g.val * (g⁻¹).val‖ := congrArg norm g.mul_inv.symm
    _ ≤ _ := norm_mul_le _ _
  rw [realMatrixHeight_eq_frobenius]
  nlinarith [sq_nonneg (‖g.val‖ - ‖(g⁻¹).val‖)]

theorem norm_entry_sq_le_realMatrixHeight (g : Langlands.GeneralLinear n ℝ) (i j : Fin n) :
    ‖g.val i j‖ ^ 2 ≤ realMatrixHeight g := by
  calc
    _ ≤ ‖g.val i j‖ ^ 2 + ‖(g⁻¹).val i j‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    _ ≤ ∑ k : Fin n, (‖g.val i k‖ ^ 2 + ‖(g⁻¹).val i k‖ ^ 2) :=
      Finset.single_le_sum (f := fun k : Fin n =>
        (‖g.val i k‖ ^ 2 + ‖(g⁻¹).val i k‖ ^ 2))
        (fun k _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
        (Finset.mem_univ j)
    _ ≤ realMatrixHeight g := by
      apply Finset.single_le_sum
        (f := fun k : Fin n => ∑ l : Fin n,
          (‖g.val k l‖ ^ 2 + ‖(g⁻¹).val k l‖ ^ 2))
        (fun k _ => Finset.sum_nonneg fun l _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
        (Finset.mem_univ i)

theorem norm_entry_le_realMatrixHeight (hn : 0 < n)
    (g : Langlands.GeneralLinear n ℝ) (i j : Fin n) :
    ‖g.val i j‖ ≤ realMatrixHeight g := by
  have hs := norm_entry_sq_le_realMatrixHeight g i j
  have hH := two_le_realMatrixHeight hn g
  nlinarith [sq_nonneg (‖g.val i j‖ - realMatrixHeight g)]

theorem norm_det_le_realMatrixHeight (hn : 0 < n) (g : Langlands.GeneralLinear n ℝ) :
    ‖g.val.det‖ ≤ (n.factorial : ℝ) * realMatrixHeight g ^ n :=
  Langlands.Global.norm_det_le_factorial_mul_pow hn g.val _ (norm_entry_le_realMatrixHeight hn g)

theorem norm_det_inv_le_realMatrixHeight (hn : 0 < n) (g : Langlands.GeneralLinear n ℝ) :
    ‖((g⁻¹).val).det‖ ≤ (n.factorial : ℝ) * realMatrixHeight g ^ n := by
  simpa only [realMatrixHeight_inv] using norm_det_le_realMatrixHeight hn g⁻¹

/-- Both signs of the real determinant exponent have polynomial growth in the matrix/inverse
height. The bound has a natural exponent depending on the given real exponent. -/
theorem exists_det_rpow_le_realMatrixHeight (hn : 0 < n) (β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear n ℝ,
      |g.val.det| ^ β ≤ C * realMatrixHeight g ^ N := by
  let k : ℕ := ⌈|β|⌉₊
  refine ⟨(n.factorial : ℝ) ^ k, n * k, by positivity, fun g => ?_⟩
  let B := (n.factorial : ℝ) * realMatrixHeight g ^ n
  have hH : 1 ≤ realMatrixHeight g := le_trans (by norm_num) (two_le_realMatrixHeight hn g)
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
    (Nat.one_le_cast.mpr (Nat.factorial_pos n)) (one_le_pow₀ hH)
  have hdet : 0 < |g.val.det| :=
    abs_pos.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hd : |g.val.det| ≤ B := by
    simpa only [Real.norm_eq_abs] using norm_det_le_realMatrixHeight hn g
  have hdi : |g.val.det|⁻¹ ≤ B := by
    have hi := norm_det_inv_le_realMatrixHeight hn g
    have he : ((g⁻¹).val).det = (g.val.det)⁻¹ := by
      have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) g.mul_inv
      rw [Matrix.det_mul, Matrix.det_one] at h
      exact inv_eq_of_mul_eq_one_right h |>.symm
    simpa only [he, Real.norm_eq_abs, abs_inv] using hi
  have hl := Langlands.Global.abs_log_le_log_of_le hdet hd hdi
  calc
    |g.val.det| ^ β = Real.exp (Real.log |g.val.det| * β) :=
      Real.rpow_def_of_pos hdet β
    _ ≤ Real.exp (Real.log B * |β|) := by
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_right hl (abs_nonneg β)))
    _ = B ^ |β| := (Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hB) _).symm
    _ ≤ B ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (Nat.le_ceil _)
    _ = (n.factorial : ℝ) ^ k * realMatrixHeight g ^ (n * k) := by
      rw [Real.rpow_natCast, mul_pow, pow_mul]

end RealPlaceRestriction
end Langlands.Global.RankinSelbergGlobal
