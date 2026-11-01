import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Fin.Basic

/-! # The first nonpositive run with ordered upper endpoints -/

namespace Langlands.Classification

open scoped BigOperators

/-- Positive lengths, ordered upper endpoints and nonpositive total endpoint
weight give a first nonpositive run. It contains every earlier interval
strictly at its lower endpoint, and is proper if there is more than one run. -/
def OrderedRunFirstNonpositive : Prop :=
  ∀ (k : ℕ) (_hk : 0 < k) (m : Fin k → ℕ) (a b : Fin k → ℝ),
    (∀ i, 0 < m i) →
    Monotone a →
    (∑ i, (m i : ℝ) * (a i + b i)) ≤ 0 →
    ∃ i : Fin k,
      a i + b i ≤ 0 ∧
      (∀ j, j < i → 0 < a j + b j ∧ b i < b j ∧ a j ≤ a i) ∧
      (1 < k → m i < ∑ j, m j)

end Langlands.Classification
