import Mathlib.Algebra.LinearRecurrence
import Mathlib.Analysis.Complex.Basic

/-!
# A uniform polynomial denominator for linear recurrence generating series

The closed proposition below states an internal analytic fact about ordinary
complex generating series of solutions of a Mathlib `LinearRecurrence`. It
supplies no proof.
-/

namespace Langlands.Analysis

/-- For every complex linear recurrence `E`, its reverse characteristic
polynomial `Q` has constant coefficient one, and some radius `ρ > 0`, chosen
from `E` alone, works for every solution `a`: on the open disc of radius `ρ`
the ordinary generating series of `a` converges, `Q` does not vanish, and the
series sum equals `A.eval z / Q.eval z` for a polynomial `A` depending on `a`. -/
def LinearRecurrenceGeneratingSeriesStatement : Prop :=
  ∀ E : LinearRecurrence ℂ,
    let Q : Polynomial ℂ :=
      1 - ∑ i : Fin E.order,
        Polynomial.C (E.coeffs i) * Polynomial.X ^ (E.order - i.val)
    Q.coeff 0 = 1 ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ a : ℕ → ℂ, E.IsSolution a →
          ∃ A : Polynomial ℂ,
            ∀ z : ℂ, ‖z‖ < ρ →
              Summable (fun n : ℕ => a n * z ^ n) ∧
                Q.eval z ≠ 0 ∧
                ∑' n : ℕ, a n * z ^ n = A.eval z / Q.eval z

end Langlands.Analysis
