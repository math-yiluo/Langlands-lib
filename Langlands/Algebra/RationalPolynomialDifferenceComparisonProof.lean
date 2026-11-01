import Langlands.Algebra.RationalPolynomialDifferenceComparisonStatement
import Langlands.Algebra.RationalPolynomialDilationProof

/-! # Polynomial coefficients from vanishing scalar differences -/

noncomputable section

open Polynomial

namespace Langlands.Algebra.RationalPolynomial

/-- The scalar difference of two polynomial sequences is its exact Newton polynomial. -/
theorem sub_eq_newtonPolynomial_of_iterate_fwdDiff_eq_zero
    (P Q : Polynomial ℚ) (r : ℚ) (d : ℕ)
    (h : (fwdDiff 1)^[d]
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) = 0) :
    Q - C r * P = newtonPolynomial
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) d := by
  apply eq_of_eventually_nat_eval_eq
  apply Filter.Eventually.of_forall
  intro n
  rw [newtonPolynomial_eval_eq _ d
    (iterate_fwdDiff_eq_zero_of_le _ h (Nat.le_succ d))]
  simp

/-- Vanishing of the d-th scalar difference identifies the d-th coefficients. -/
theorem coeff_eq_of_iterate_fwdDiff_sub_eq_zero
    (P Q : Polynomial ℚ) (r : ℚ) (d : ℕ)
    (h : (fwdDiff 1)^[d]
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) = 0) :
    Q.coeff d = r * P.coeff d := by
  have he := congrArg (fun R : Polynomial ℚ => R.coeff d)
    (sub_eq_newtonPolynomial_of_iterate_fwdDiff_eq_zero P Q r d h)
  rw [newtonPolynomial_coeff, h] at he
  have he0 : Q.coeff d - r * P.coeff d = 0 := by simpa using he
  exact sub_eq_zero.mp he0

/-- If the source has exact degree d and r is nonzero, the target has the same
exact degree and its leading coefficient is multiplied by r. -/
theorem natDegree_leadingCoeff_of_iterate_fwdDiff_sub_eq_zero
    (P Q : Polynomial ℚ) (r : ℚ) (d : ℕ)
    (hp : P ≠ 0) (hd : P.natDegree = d) (hr : r ≠ 0)
    (h : (fwdDiff 1)^[d]
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) = 0) :
    Q.natDegree = d ∧ Q.leadingCoeff = r * P.leadingCoeff := by
  have hcoeff := coeff_eq_of_iterate_fwdDiff_sub_eq_zero P Q r d h
  have hsub : (Q - C r * P).natDegree ≤ d := by
    rw [sub_eq_newtonPolynomial_of_iterate_fwdDiff_eq_zero P Q r d h]
    exact newtonPolynomial_natDegree_le _ d
  have hmul : (C r * P).natDegree ≤ d := (natDegree_C_mul_le r P).trans hd.le
  have hQ : Q.natDegree ≤ d := (natDegree_sub_le_iff_left hmul).mp hsub
  have hc : Q.coeff d ≠ 0 := by
    rw [hcoeff, ← hd, coeff_natDegree]
    exact mul_ne_zero hr (leadingCoeff_ne_zero.mpr hp)
  have hQd := natDegree_eq_of_le_of_coeff_ne_zero hQ hc
  exact ⟨hQd, by simpa only [leadingCoeff, hQd, hd] using hcoeff⟩

end Langlands.Algebra.RationalPolynomial

namespace Langlands.Algebra

/-- The complete rational scalar-difference coefficient interface. -/
theorem rationalPolynomialDifferenceComparison :
    RationalPolynomialDifferenceComparisonStatement :=
  ⟨RationalPolynomial.sub_eq_newtonPolynomial_of_iterate_fwdDiff_eq_zero,
    RationalPolynomial.coeff_eq_of_iterate_fwdDiff_sub_eq_zero,
    RationalPolynomial.natDegree_leadingCoeff_of_iterate_fwdDiff_sub_eq_zero⟩

end Langlands.Algebra
