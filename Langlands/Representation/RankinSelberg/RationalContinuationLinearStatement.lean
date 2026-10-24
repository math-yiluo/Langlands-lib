import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalZeta

/-! Finite linear combinations of continuations and fixed-denominator closure. -/

noncomputable section

namespace Langlands.RankinSelberg

open scoped BigOperators

/-- Continuations respect finite complex linear combinations, and a fixed
Laurent denominator clearing a set also clears its Laurent span. -/
def RationalContinuationLinearStatement : Prop :=
  (∀ (q r : ℕ) (f : Fin r → ℂ → ℂ)
      (R : Fin r → RationalFunctions) (c : Fin r → ℂ),
    (∀ i, HasRationalContinuation q (f i) (R i)) →
    HasRationalContinuation q (fun s => ∑ i, c i * f i s)
      (∑ i, RatFunc.C (c i) * R i)) ∧
  (∀ (values : Set RationalFunctions) (d : LaurentCoefficients),
    (∀ R ∈ values, ∃ P : LaurentCoefficients,
      laurentToRatFunc P = laurentToRatFunc d * R) →
    ∀ R ∈ zetaSpan values, ∃ P : LaurentCoefficients,
      laurentToRatFunc P = laurentToRatFunc d * R)

end Langlands.RankinSelberg
