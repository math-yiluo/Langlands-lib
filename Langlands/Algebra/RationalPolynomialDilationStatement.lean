import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Uniqueness and dilation of rational polynomials -/

open Filter Polynomial

namespace Langlands.Algebra

/-- Arithmetic for rational polynomials that agree, or agree after a dilation,
at all sufficiently large natural numbers. -/
def RationalPolynomialDilationStatement : Prop :=
  (∀ (P Q : Polynomial ℚ),
    (∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) → P = Q) ∧
  (∀ (P Q : Polynomial ℚ) (q : ℕ),
    (∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = P.eval ((q * n : ℕ) : ℚ)) →
      Q = P.comp (C (q : ℚ) * X)) ∧
  (∀ (P : Polynomial ℚ) (q : ℕ), 0 < q →
    (P.comp (C (q : ℚ) * X)).natDegree = P.natDegree ∧
      (P.comp (C (q : ℚ) * X)).leadingCoeff =
        P.leadingCoeff * (q : ℚ) ^ P.natDegree) ∧
  (∀ (P Q : Polynomial ℚ) (q r g : ℕ),
    P ≠ 0 → P.natDegree = g → 0 < q →
      (∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = P.eval ((q * n : ℕ) : ℚ)) →
      Q.leadingCoeff = (r : ℚ) * P.leadingCoeff →
        r = q ^ g)

end Langlands.Algebra
