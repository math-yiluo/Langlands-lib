import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Numerical helpers for the commuting-endomorphism dimension argument. -/

namespace Langlands.CommutingDimension

/-- The real exponent appearing in the commuting dimension estimate. -/
noncomputable def dimensionExponent (l : ℕ) : ℝ := 2 - 2 / (2 : ℝ) ^ l

@[simp] theorem dimensionExponent_zero : dimensionExponent 0 = 0 := by
  norm_num [dimensionExponent]

theorem dimensionExponent_succ_ge_one (l : ℕ) :
    1 ≤ dimensionExponent (l + 1) := by
  have hp : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ l := by positivity
  dsimp [dimensionExponent]
  rw [pow_succ]
  apply le_sub_iff_add_le.mpr
  have : 2 / ((2 : ℝ) ^ l * 2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith

theorem dimensionExponent_recurrence (l : ℕ) :
    dimensionExponent l = 2 * dimensionExponent (l + 1) - 2 := by
  dsimp [dimensionExponent]
  rw [pow_succ]
  field_simp
  ring

/-- The two algebraic estimates close the dimension induction for any exponent at least one. -/
theorem real_dimension_step (m s D r : ℝ) (hm : 0 < m) (hs : 0 ≤ s)
    (hsm : s ≤ m) (hr : 1 ≤ r)
    (hgenerate : D ≤ s * m)
    (hsplit : D ≤ (m - s) ^ r + m ^ (2 * r - 2)) :
    D ≤ m ^ r := by
  have hmr : m * m ^ (r - 1) = m ^ r := by
    rw [← Real.rpow_one_add' hm.le (by linarith : 1 + (r - 1) ≠ 0)]
    congr 1
    ring
  have hprev : m ^ (2 * r - 2) = (m ^ (r - 1)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hm]
    congr 1
    ring
  have hsmall : (m - s) ^ r ≤ (m - s) * m ^ (r - 1) := by
    calc
      _ = (m - s) * (m - s) ^ (r - 1) := by
        rw [← Real.rpow_one_add' (sub_nonneg.mpr hsm) (by linarith : 1 + (r - 1) ≠ 0)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sub_nonneg.mpr hsm) (by linarith) (by linarith))
        (sub_nonneg.mpr hsm)
  have hpos : 0 < m ^ (r - 1) := Real.rpow_pos_of_pos hm _
  rw [hprev] at hsplit
  by_contra! hD
  have hs' : m ^ (r - 1) < s := by nlinarith
  have hstrict := mul_pos (sub_pos.mpr hs') hpos
  nlinarith

end Langlands.CommutingDimension
