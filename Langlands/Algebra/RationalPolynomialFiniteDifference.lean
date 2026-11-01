import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Positivity

/-! # Rational Newton polynomials for sequences with vanishing differences -/

noncomputable section

open Polynomial Finset

namespace Langlands.Algebra.RationalPolynomial

/-- The truncated Newton polynomial, expressed in the falling-factorial basis. -/
def newtonPolynomial (f : ℕ → ℚ) (d : ℕ) : Polynomial ℚ :=
  ∑ k ∈ range (d + 1),
    C (((fwdDiff 1)^[k] f) 0 / (k.factorial : ℚ)) * descPochhammer ℚ k

theorem newtonPolynomial_natDegree_le (f : ℕ → ℚ) (d : ℕ) :
    (newtonPolynomial f d).natDegree ≤ d := by
  unfold newtonPolynomial
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans
    ((descPochhammer_natDegree ℚ k).le.trans (Nat.le_of_lt_succ (mem_range.mp hk)))

theorem newtonPolynomial_eval (f : ℕ → ℚ) (d n : ℕ) :
    (newtonPolynomial f d).eval (n : ℚ) =
      ∑ k ∈ range (d + 1), (n.choose k : ℚ) * ((fwdDiff 1)^[k] f) 0 := by
  simp only [newtonPolynomial, eval_finsetSum, eval_mul, eval_C]
  apply sum_congr rfl
  intro k _
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

theorem iterate_fwdDiff_eq_zero_of_le (f : ℕ → ℚ) {r k : ℕ}
    (h : (fwdDiff 1)^[r] f = 0) (hrk : r ≤ k) :
    (fwdDiff 1)^[k] f = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrk
  clear hrk
  rw [Nat.add_comm, Function.iterate_add_apply, h]
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [Function.iterate_succ_apply', ih]
      exact fwdDiff_const 1 0

/-- Vanishing of the next difference makes the truncated Newton formula exact
at every natural argument, including zero. -/
theorem newtonPolynomial_eval_eq (f : ℕ → ℚ) (d : ℕ)
    (h : (fwdDiff 1)^[d + 1] f = 0) (n : ℕ) :
    (newtonPolynomial f d).eval (n : ℚ) = f n := by
  rw [newtonPolynomial_eval]
  have hn := shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  simp only [nsmul_eq_mul, Nat.cast_id, mul_one, zero_add] at hn
  rw [hn]
  apply sum_congr_of_eq_on_inter
  · intro k hk hkn
    have hnk : n < k := by simpa using hkn
    simp [Nat.choose_eq_zero_of_lt hnk]
  · intro k hk hkd
    have hdk : d + 1 ≤ k := by simpa using hkd
    rw [iterate_fwdDiff_eq_zero_of_le f h hdk]
    simp
  · intro k _ _
    rfl

/-- The top Newton coefficient records the top difference divided by a
factorial, even if the polynomial's actual degree is smaller. -/
theorem newtonPolynomial_coeff (f : ℕ → ℚ) (d : ℕ) :
    (newtonPolynomial f d).coeff d =
      ((fwdDiff 1)^[d] f) 0 / (d.factorial : ℚ) := by
  rw [newtonPolynomial, sum_range_succ, coeff_add, coeff_C_mul]
  have hz : (∑ k ∈ range d,
      C (((fwdDiff 1)^[k] f) 0 / (k.factorial : ℚ)) * descPochhammer ℚ k).coeff d = 0 := by
    rw [finsetSum_coeff]
    apply sum_eq_zero
    intro k hk
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    simpa only [descPochhammer_natDegree] using mem_range.mp hk
  rw [hz, zero_add]
  have hm := monic_descPochhammer ℚ d
  have hc : (descPochhammer ℚ d).coeff d = 1 := by
    simpa only [descPochhammer_natDegree] using hm.coeff_natDegree
  rw [hc, mul_one]

/-- A positive top difference gives exact degree and positive leading term. -/
theorem newtonPolynomial_degree_leadingCoeff_pos (f : ℕ → ℚ) (d : ℕ)
    (h : 0 < ((fwdDiff 1)^[d] f) 0) :
    (newtonPolynomial f d).natDegree = d ∧
      0 < (newtonPolynomial f d).leadingCoeff := by
  have hc : 0 < (newtonPolynomial f d).coeff d := by
    rw [newtonPolynomial_coeff]
    exact div_pos h (by positivity)
  have hd : (newtonPolynomial f d).natDegree = d :=
    le_antisymm (newtonPolynomial_natDegree_le f d)
      (le_natDegree_of_ne_zero (ne_of_gt hc))
  exact ⟨hd, by simpa only [leadingCoeff, hd] using hc⟩

end Langlands.Algebra.RationalPolynomial
