import Langlands.Algebra.RationalPolynomialFiniteDifference
import Mathlib.Tactic.FieldSimp

/-! # Denominators of Newton polynomials of integer-valued sequences

If a rational sequence takes integer values, then every coefficient of its
truncated Newton polynomial of degree at most `d` becomes an integer after
multiplication by `d!`. -/

noncomputable section

open Polynomial Finset

namespace Langlands.Algebra.RationalPolynomial

/-- Iterated forward differences of an integer-valued sequence are integer-valued. -/
theorem iterate_fwdDiff_mem_intCast_range (f : ℕ → ℚ)
    (hf : ∀ n, f n ∈ (Int.castRingHom ℚ).range) (k n : ℕ) :
    ((fwdDiff 1)^[k] f) n ∈ (Int.castRingHom ℚ).range := by
  induction k generalizing n with
  | zero => exact hf n
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Subring.sub_mem _ (ih (n + 1)) (ih n)

/-- For an integer-valued sequence, `d!` times any coefficient of the
degree-`d` truncated Newton polynomial is an integer. -/
theorem factorial_mul_coeff_newtonPolynomial_mem (f : ℕ → ℚ)
    (hf : ∀ n, f n ∈ (Int.castRingHom ℚ).range) (d j : ℕ) :
    (d.factorial : ℚ) * (newtonPolynomial f d).coeff j ∈ (Int.castRingHom ℚ).range := by
  rw [newtonPolynomial, finsetSum_coeff, Finset.mul_sum]
  refine Subring.sum_mem _ fun k hk => ?_
  rw [coeff_C_mul]
  have hkd : k ≤ d := Nat.le_of_lt_succ (mem_range.mp hk)
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hkd
  have hk0 : (k.factorial : ℚ) ≠ 0 := by positivity
  have heq : (d.factorial : ℚ) *
      (((fwdDiff 1)^[k] f) 0 / (k.factorial : ℚ) * (descPochhammer ℚ k).coeff j) =
      (m : ℚ) * ((fwdDiff 1)^[k] f) 0 * (descPochhammer ℚ k).coeff j := by
    rw [hm, Nat.cast_mul]
    field_simp
  rw [heq]
  refine Subring.mul_mem _ (Subring.mul_mem _ ⟨(m : ℤ), by simp⟩
    (iterate_fwdDiff_mem_intCast_range f hf k 0)) ?_
  rw [← descPochhammer_map (Int.castRingHom ℚ), coeff_map]
  exact ⟨_, rfl⟩

/-- The same denominator bound for a difference of two Newton polynomials. -/
theorem factorial_mul_coeff_newtonPolynomial_sub_mem (f g : ℕ → ℚ)
    (hf : ∀ n, f n ∈ (Int.castRingHom ℚ).range)
    (hg : ∀ n, g n ∈ (Int.castRingHom ℚ).range) (d j : ℕ) :
    (d.factorial : ℚ) * (newtonPolynomial f d - newtonPolynomial g d).coeff j ∈
      (Int.castRingHom ℚ).range := by
  rw [coeff_sub, mul_sub]
  exact Subring.sub_mem _ (factorial_mul_coeff_newtonPolynomial_mem f hf d j)
    (factorial_mul_coeff_newtonPolynomial_mem g hg d j)

end Langlands.Algebra.RationalPolynomial
