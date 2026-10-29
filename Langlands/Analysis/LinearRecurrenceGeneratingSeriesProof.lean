import Mathlib.Analysis.SpecificLimits.Normed
import Langlands.Analysis.LinearRecurrenceGeneratingSeriesStatement

/-!
# Proof of the uniform polynomial denominator for linear recurrence series

For a complex linear recurrence `E` with coefficients `c` and order `d`, put
`S = ∑ i, ‖c i‖`. Every solution `a` satisfies `‖a n‖ ≤ C * (1 + S) ^ n`
with `C = ∑ j < d, ‖a j‖`, so its generating series converges absolutely on
the disc `‖z‖ < 1 / (1 + S)`. On that disc the reverse characteristic
polynomial `Q` does not vanish, and shifting the series by `d` terms gives
`Q(z) * ∑ a n z ^ n = A(z)` for an explicit polynomial `A`.
-/

namespace Langlands.Analysis

open Finset Polynomial

namespace LinearRecurrenceGeneratingSeries

/-- A solution of a complex linear recurrence grows at most geometrically, with
ratio `1 + ∑ i, ‖E.coeffs i‖` and constant `∑ j < E.order, ‖a j‖`. -/
theorem norm_le_geometric (E : LinearRecurrence ℂ) {a : ℕ → ℂ} (ha : E.IsSolution a)
    (n : ℕ) :
    ‖a n‖ ≤ (∑ j ∈ range E.order, ‖a j‖) * (1 + ∑ i, ‖E.coeffs i‖) ^ n := by
  set C := ∑ j ∈ range E.order, ‖a j‖ with hCdef
  set S := ∑ i, ‖E.coeffs i‖ with hSdef
  have hS : 0 ≤ S := sum_nonneg fun i _ => norm_nonneg _
  have hC : 0 ≤ C := sum_nonneg fun j _ => norm_nonneg _
  have hR : 1 ≤ 1 + S := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < E.order
    · calc ‖a n‖ ≤ C :=
            single_le_sum (f := fun j => ‖a j‖) (fun j _ => norm_nonneg _) (mem_range.2 hn)
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (1 + S) ^ n := mul_le_mul_of_nonneg_left (one_le_pow₀ hR) hC
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + E.order := ⟨n - E.order, by omega⟩
      rw [ha m]
      by_cases hd : E.order = 0
      · have hsum : ∑ i : Fin E.order, E.coeffs i * a (m + i) = 0 := by
          apply sum_eq_zero
          intro i _
          exact absurd i.isLt (by omega)
        rw [hsum, norm_zero]
        exact mul_nonneg hC (pow_nonneg (by linarith) _)
      calc ‖∑ i, E.coeffs i * a (m + i)‖ ≤ ∑ i, ‖E.coeffs i * a (m + i)‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin E.order, ‖E.coeffs i‖ * (C * (1 + S) ^ (m + E.order - 1)) := by
          gcongr with i
          rw [norm_mul]
          gcongr
          calc ‖a (m + i)‖ ≤ C * (1 + S) ^ (m + i) := ih _ (by have := i.isLt; omega)
            _ ≤ C * (1 + S) ^ (m + E.order - 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by have := i.isLt; omega)) hC
        _ = S * (C * (1 + S) ^ (m + E.order - 1)) := by rw [← sum_mul]
        _ ≤ (1 + S) * (C * (1 + S) ^ (m + E.order - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC (pow_nonneg (by linarith) _))
        _ = C * (1 + S) ^ (m + E.order) := by
          have he : m + E.order = (m + E.order - 1) + 1 := by omega
          rw [he, pow_succ]
          simp only [Nat.add_sub_cancel]
          ring

/-- The reverse characteristic polynomial has constant coefficient one. -/
theorem coeff_zero_reverse (E : LinearRecurrence ℂ) :
    (1 - ∑ i : Fin E.order,
        Polynomial.C (E.coeffs i) * Polynomial.X ^ (E.order - i.val)).coeff 0 = 1 := by
  rw [coeff_sub, coeff_one_zero, finsetSum_coeff]
  have hsum : ∑ i : Fin E.order,
      (Polynomial.C (E.coeffs i) * Polynomial.X ^ (E.order - i.val)).coeff 0 = 0 := by
    apply sum_eq_zero
    intro i _
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · have := i.isLt
      omega
    · exact mul_zero _
  rw [hsum, sub_zero]

end LinearRecurrenceGeneratingSeries

open LinearRecurrenceGeneratingSeries in
/-- Proof of `LinearRecurrenceGeneratingSeriesStatement`, with radius
`ρ = 1 / (1 + ∑ i, ‖E.coeffs i‖)`. -/
theorem linearRecurrenceGeneratingSeriesStatement_proof :
    LinearRecurrenceGeneratingSeriesStatement := by
  intro E Q
  set S := ∑ i, ‖E.coeffs i‖ with hSdef
  have hS : 0 ≤ S := sum_nonneg fun i _ => norm_nonneg _
  have hpos : 0 < 1 + S := by linarith
  refine ⟨coeff_zero_reverse E, 1 / (1 + S), by positivity, ?_⟩
  intro a ha
  let A : Polynomial ℂ :=
    ∑ j ∈ range E.order, Polynomial.C (a j) * Polynomial.X ^ j -
      ∑ i : Fin E.order, Polynomial.C (E.coeffs i) * Polynomial.X ^ (E.order - i.val) *
        ∑ j ∈ range i.val, Polynomial.C (a j) * Polynomial.X ^ j
  refine ⟨A, fun z hz => ?_⟩
  have hz' : ‖z‖ * (1 + S) < 1 := (lt_div_iff₀ hpos).1 hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz1 : ‖z‖ ≤ 1 := by nlinarith
  -- Summability from the geometric bound.
  have hsum : Summable (fun n : ℕ => a n * z ^ n) := by
    set C := ∑ j ∈ range E.order, ‖a j‖
    have hr0 : 0 ≤ (1 + S) * ‖z‖ := by positivity
    have hr1 : (1 + S) * ‖z‖ < 1 := by linarith
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C) (fun n => ?_)
    rw [norm_mul, norm_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_le_geometric E ha n) (pow_nonneg hz0 n)
  -- The reverse characteristic polynomial does not vanish on the disc.
  have hQeval : Q.eval z = 1 - ∑ i : Fin E.order, E.coeffs i * z ^ (E.order - i.val) := by
    simp [Q, eval_finsetSum]
  have hQ : Q.eval z ≠ 0 := by
    rw [hQeval]
    intro h0
    have h1 : ∑ i : Fin E.order, E.coeffs i * z ^ (E.order - i.val) = 1 := by
      linear_combination -h0
    have hle : ‖∑ i : Fin E.order, E.coeffs i * z ^ (E.order - i.val)‖ ≤ S * ‖z‖ := by
      calc ‖∑ i : Fin E.order, E.coeffs i * z ^ (E.order - i.val)‖
          ≤ ∑ i : Fin E.order, ‖E.coeffs i * z ^ (E.order - i.val)‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin E.order, ‖E.coeffs i‖ * ‖z‖ := by
          gcongr with i
          rw [norm_mul, norm_pow]
          gcongr
          exact pow_le_of_le_one hz0 hz1 (by have := i.isLt; omega)
        _ = S * ‖z‖ := by rw [← sum_mul]
    rw [h1, norm_one] at hle
    nlinarith
  refine ⟨hsum, hQ, ?_⟩
  -- Shift the series by `E.order` terms and apply the recurrence.
  set F := ∑' n : ℕ, a n * z ^ n with hF
  have hshift : ∀ k : ℕ,
      ∑' n : ℕ, a (n + k) * z ^ (n + k) = F - ∑ j ∈ range k, a j * z ^ j := by
    intro k
    have h := hsum.sum_add_tsum_nat_add k
    rw [hF]
    linear_combination h
  have hsumk : ∀ k : ℕ, Summable (fun n : ℕ => a (n + k) * z ^ (n + k)) := fun k =>
    (summable_nat_add_iff k).2 hsum
  have key : F - ∑ j ∈ range E.order, a j * z ^ j =
      ∑ i : Fin E.order,
        E.coeffs i * z ^ (E.order - i.val) * (F - ∑ j ∈ range i.val, a j * z ^ j) := by
    rw [← hshift E.order]
    have hterm : ∀ n : ℕ, a (n + E.order) * z ^ (n + E.order) =
        ∑ i : Fin E.order,
          E.coeffs i * z ^ (E.order - i.val) * (a (n + i.val) * z ^ (n + i.val)) := by
      intro n
      rw [ha n, sum_mul]
      refine sum_congr rfl fun i _ => ?_
      have he : n + E.order = (n + i.val) + (E.order - i.val) := by have := i.isLt; omega
      rw [he, pow_add]
      ring
    simp_rw [hterm]
    have hs : ∀ i ∈ (univ : Finset (Fin E.order)), Summable (fun n : ℕ =>
        E.coeffs i * z ^ (E.order - i.val) * (a (n + i.val) * z ^ (n + i.val))) :=
      fun i _ => (hsumk i.val).mul_left _
    rw [Summable.tsum_finsetSum hs]
    refine sum_congr rfl fun i _ => ?_
    rw [tsum_mul_left, hshift]
  rw [eq_div_iff hQ, hQeval]
  simp only [A, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  simp only [mul_sub, sum_sub_distrib] at key
  rw [← sum_mul] at key
  linear_combination key

end Langlands.Analysis
