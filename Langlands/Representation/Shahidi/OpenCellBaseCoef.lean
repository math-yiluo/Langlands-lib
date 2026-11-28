import Langlands.Representation.Shahidi.OpenCellBaseSchur

/-! # The constants of the `(1, n)` shell identity

For `q > 0` and `D ≤ t + 1`, the product of the modulus factor
`(q^(-(t+2) D))^(1/2 + s/(t+2))`, the power `q^(α(t+1,D))` and the half modulus at `κ(t, D)` is
`(q^(-(1+s)))^D`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical

theorem baseAlpha_two_mul (t D : ℕ) (hD : D ≤ t + 1) :
    2 * (baseAlpha (t + 1) D : ℤ) = 2 * D * t - D * (D - 1) := by
  induction D with
  | zero => simp [baseAlpha]
  | succ D ih =>
    have ih' := ih (by omega)
    simp only [baseAlpha] at ih' ⊢
    rw [Finset.sum_range_succ, Nat.cast_add, mul_add, ih']
    have h : ((t + 1 - 1 - D : ℕ) : ℤ) = t - D := by
      rw [show t + 1 - 1 - D = t - D by omega]
      push_cast [show D ≤ t by omega]
      ring
    rw [h]
    push_cast
    ring

theorem baseKappa_succ_apply {t D : ℕ} (hD : D ≤ t) (i : Fin (t + 1)) :
    baseKappa t (D + 1) i = baseKappa t D i - if (i : ℕ) = t - D then 1 else 0 := by
  simp only [baseKappa]
  split_ifs <;> omega

theorem sum_weight_baseKappa (t D : ℕ) (hD : D ≤ t + 1) :
    ∑ i : Fin (t + 1), ((t : ℤ) - 2 * (i : ℤ)) * baseKappa t D i = D * t - D * D + D := by
  induction D with
  | zero =>
    simp only [baseKappa_zero, mul_zero, Finset.sum_const_zero]
    ring
  | succ D ih =>
    have ih' := ih (by omega)
    have hDt : D ≤ t := by omega
    simp_rw [baseKappa_succ_apply hDt, mul_sub, Finset.sum_sub_distrib, ih', mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single (⟨t - D, by omega⟩ : Fin (t + 1))]
    · rw [ite_eq_left rfl]
      push_cast [hDt]
      ring
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      exact hb (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem natCast_cpow_eq (q : ℕ) (hq : 0 < q) (m : ℤ) (w : ℂ) :
    ((((q : ℝ) ^ m : ℝ) : ℂ)) ^ w = (q : ℂ) ^ ((m : ℂ) * w) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast, ← Complex.cpow_intCast]
  rw [← Complex.cpow_mul]
  · have hlog : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hq0.le]
    rw [hlog]
    simp only [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact neg_lt_zero.2 Real.pi_pos
  · have hlog : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hq0.le]
    rw [hlog]
    simp only [← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact Real.pi_pos.le

theorem halfModulus_eq_cpow (q : ℕ) {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    halfModulus q lam =
      (q : ℂ) ^ (((-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i : ℤ) : ℂ) * (1 / 2)) := by
  rw [halfModulus, Complex.cpow_int_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  norm_num

/-- **The constant of the shell identity.** -/
theorem baseConstant_eq (q : ℕ) (hq : 0 < q) (t D : ℕ) (hD : D ≤ t + 1) (s : ℂ) :
    ((((q : ℝ) ^ (-(((0 + t + 2 : ℕ) : ℤ) * (D : ℤ))) : ℝ) : ℂ) ^
        ((1 : ℂ) / 2 + s / ((0 + t + 2 : ℕ) : ℂ))) * (q : ℂ) ^ (baseAlpha (t + 1) D) *
        halfModulus q (baseKappa t D) =
      ((q : ℂ) ^ (-(1 + s))) ^ D := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [natCast_cpow_eq q hq, halfModulus_eq_cpow, sum_weight_baseKappa t D hD,
    ← Complex.cpow_natCast (q : ℂ) (baseAlpha (t + 1) D), ← Complex.cpow_add _ _ hq0,
    ← Complex.cpow_add _ _ hq0, ← Complex.cpow_nat_mul]
  congr 1
  have hα := baseAlpha_two_mul t D hD
  have hα' : (baseAlpha (t + 1) D : ℂ) = ((2 * D * t - D * (D - 1) : ℤ) : ℂ) / 2 := by
    rw [← hα]
    push_cast
    ring
  rw [hα']
  have hN : ((0 + t + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 0 + t + 2 ≠ 0)
  have key := div_mul_cancel₀ s hN
  push_cast at key ⊢
  linear_combination (-(D : ℂ)) * key

end Langlands.Shahidi.OpenCell.Base
