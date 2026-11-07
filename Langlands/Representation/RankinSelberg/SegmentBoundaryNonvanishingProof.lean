import Langlands.Representation.RankinSelberg.SegmentBoundaryNonvanishingStatement

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial SegmentGammaTelescoping

namespace SegmentGammaTelescoping

@[simp]
theorem linearFactor_eval (a : ℂˣ) (z : ℂ) :
    (linearFactor a).eval z = 1 - (a : ℂ) * z := by
  simp [linearFactor]

theorem linearFactor_eval_ne_zero (a : ℂˣ) (ha : ‖(a : ℂ)‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) : (linearFactor a).eval z ≠ 0 := by
  rw [linearFactor_eval]
  intro he
  have he' : (a : ℂ) * z = 1 := (sub_eq_zero.mp he).symm
  have hlt : ‖(a : ℂ) * z‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha (norm_nonneg z))
      (by simpa using hz)
  rw [he', norm_one] at hlt
  exact lt_irrefl _ hlt

theorem boundaryPolynomial_eval_ne_zero (a t : ℂˣ) {m n : ℕ}
    (hnm : n ≤ m) (ht : ‖(t : ℂ)‖ ≤ 1) (ha : ‖(a : ℂ)‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    (boundaryPolynomial a t m n).eval z ≠ 0 := by
  classical
  rw [boundaryPolynomial, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply linearFactor_eval_ne_zero _ _ z hz
  have hj : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
  have he : (0 : ℤ) ≤ blockExponent m n 0 j.val := by
    simp only [blockExponent]
    omega
  rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow]
  calc
    ‖(a : ℂ)‖ * ‖(t : ℂ)‖ ^ blockExponent m n 0 j.val ≤
        1 * ‖(t : ℂ)‖ ^ blockExponent m n 0 j.val :=
      mul_le_mul_of_nonneg_right ha (zpow_nonneg (norm_nonneg _) _)
    _ ≤ 1 := by
      simpa using zpow_le_one₀ (norm_pos_iff.mpr t.ne_zero) ht he

@[simp]
theorem boundaryPolynomial_coeff_zero (a t : ℂˣ) (m n : ℕ) :
    (boundaryPolynomial a t m n).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, boundaryPolynomial, eval_prod]
  simp [linearFactor]

end SegmentGammaTelescoping

theorem segmentBoundaryNonvanishing : SegmentBoundaryNonvanishingStatement := by
  classical
  intro A t m n hnm ht hA z hz
  rw [eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun a ha =>
    boundaryPolynomial_eval_ne_zero a t hnm ht (hA a ha) z hz

end Langlands.RankinSelberg
