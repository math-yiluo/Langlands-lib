import Langlands.Algebra.RenardNilpotentDimensionMaximum
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Langlands.Renard

/-- Renard C.I: the floor recurrence for the actual maximum and its descent index. -/
def NilpotentDimensionFloorRecurrenceStatement : Prop :=
  ∀ (l k : ℕ), 1 ≤ l → 1 ≤ k →
    let q : ℝ := (k : ℝ) - (nilpotentGeneratedPhi l k : ℝ) / (k : ℝ)
    0 ≤ q ∧
      ⌊q⌋₊ < k ∧
      nilpotentGeneratedPhi l k ≤
        nilpotentGeneratedPhi l ⌊q⌋₊ +
          nilpotentGeneratedPhi (l - 1) k

end Langlands.Renard
