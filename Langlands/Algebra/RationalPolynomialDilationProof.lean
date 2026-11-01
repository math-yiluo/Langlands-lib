import Langlands.Algebra.RationalPolynomialDilationStatement
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-! # Uniqueness and dilation of rational polynomials -/

open Filter Polynomial

namespace Langlands.Algebra

namespace RationalPolynomial

/-- Equality on a natural-number tail determines a rational polynomial. -/
theorem eq_of_eventually_nat_eval_eq (P Q : Polynomial ℚ)
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) :
    P = Q := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply Polynomial.eq_of_infinite_eval_eq P Q
  apply ((Set.Ici_infinite N).image (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro _ ⟨n, hn, rfl⟩
  exact hN n hn

/-- An eventual dilation identity is the corresponding composition identity. -/
theorem eq_comp_of_eventually_nat_eval_dilation (P Q : Polynomial ℚ) (q : ℕ)
    (h : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = P.eval ((q * n : ℕ) : ℚ)) :
    Q = P.comp (C (q : ℚ) * X) := by
  apply eq_of_eventually_nat_eval_eq
  exact h.mono fun n hn ↦ by
    simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Nat.cast_mul] using hn

/-- Positive dilation preserves natural degree and scales the leading coefficient. -/
theorem dilation_natDegree_leadingCoeff (P : Polynomial ℚ) (q : ℕ) (hq : 0 < q) :
    (P.comp (C (q : ℚ) * X)).natDegree = P.natDegree ∧
      (P.comp (C (q : ℚ) * X)).leadingCoeff =
        P.leadingCoeff * (q : ℚ) ^ P.natDegree := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hd : (P.comp (C (q : ℚ) * X)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ hq0, mul_one]
  refine ⟨hd, ?_⟩
  change (P.comp (C (q : ℚ) * X)).coeff
    (P.comp (C (q : ℚ) * X)).natDegree = _
  rw [hd, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_natDegree]

/-- Cancel a nonzero leading coefficient after an eventual dilation identity. -/
theorem scalar_eq_pow_of_eventually_nat_eval_dilation
    (P Q : Polynomial ℚ) (q r g : ℕ)
    (hp : P ≠ 0) (hdeg : P.natDegree = g) (hq : 0 < q)
    (h : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = P.eval ((q * n : ℕ) : ℚ))
    (hc : Q.leadingCoeff = (r : ℚ) * P.leadingCoeff) :
    r = q ^ g := by
  have heq := eq_comp_of_eventually_nat_eval_dilation P Q q h
  have hscalar : (r : ℚ) = (q : ℚ) ^ g := by
    apply mul_left_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp)
    calc
      P.leadingCoeff * (r : ℚ) = Q.leadingCoeff := by rw [hc, mul_comm]
      _ = P.leadingCoeff * (q : ℚ) ^ g := by
        rw [heq, (dilation_natDegree_leadingCoeff P q hq).2, hdeg]
  apply Nat.cast_injective (R := ℚ)
  simpa only [Nat.cast_pow] using hscalar

end RationalPolynomial

/-- The full rational-polynomial arithmetic interface. -/
theorem rationalPolynomialDilation : RationalPolynomialDilationStatement :=
  ⟨RationalPolynomial.eq_of_eventually_nat_eval_eq,
    RationalPolynomial.eq_comp_of_eventually_nat_eval_dilation,
    RationalPolynomial.dilation_natDegree_leadingCoeff,
    RationalPolynomial.scalar_eq_pow_of_eventually_nat_eval_dilation⟩

end Langlands.Algebra
