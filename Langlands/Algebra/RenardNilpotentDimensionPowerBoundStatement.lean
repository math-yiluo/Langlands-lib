import Langlands.Algebra.RenardNilpotentDimensionMaximum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The exact source real-power bound on the actual canonical nilpotent maximum. -/

namespace Langlands.Renard

/-- Renard C.I's bound on the actual canonical maximum, including the elementary boundaries. -/
def NilpotentDimensionPowerBoundStatement : Prop :=
  ∀ l k : ℕ,
    (nilpotentGeneratedPhi l k : ℝ) ≤
      Real.rpow (k : ℝ) (2 - Real.rpow 2 (1 - (l : ℝ)))

end Langlands.Renard
