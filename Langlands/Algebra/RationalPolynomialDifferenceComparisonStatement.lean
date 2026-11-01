import Mathlib.Algebra.Group.ForwardDiff
import Langlands.Algebra.RationalPolynomialFiniteDifference

/-! # Coefficient comparison from vanishing polynomial scalar differences -/

open Polynomial

namespace Langlands.Algebra

/-- Newton reconstruction, top coefficient comparison, and exact leading-term
comparison for a scalar difference with vanishing d-th forward difference. -/
def RationalPolynomialDifferenceComparisonStatement : Prop :=
  (∀ (P Q : Polynomial ℚ) (r : ℚ) (d : ℕ),
    (fwdDiff 1)^[d]
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) = 0 →
    Q - C r * P = RationalPolynomial.newtonPolynomial
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) d) ∧
  (∀ (P Q : Polynomial ℚ) (r : ℚ) (d : ℕ),
    (fwdDiff 1)^[d]
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) = 0 →
    Q.coeff d = r * P.coeff d) ∧
  (∀ (P Q : Polynomial ℚ) (r : ℚ) (d : ℕ),
    P ≠ 0 → P.natDegree = d → r ≠ 0 →
    (fwdDiff 1)^[d]
      ((fun n : ℕ => Q.eval (n : ℚ)) - fun n : ℕ => r * P.eval (n : ℚ)) = 0 →
    Q.natDegree = d ∧ Q.leadingCoeff = r * P.leadingCoeff)

end Langlands.Algebra
