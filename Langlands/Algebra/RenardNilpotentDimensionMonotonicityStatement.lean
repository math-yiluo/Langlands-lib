import Langlands.Algebra.RenardNilpotentDimensionMaximum

universe u v

namespace Langlands.Renard

/-- Renard C.I: the maximum for a fixed generator count is nondecreasing in dimension. -/
def NilpotentDimensionMonotonicityStatement : Prop :=
  (∀ (l : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
      [FiniteDimensional ℂ V] (W : Type v) [AddCommGroup W] [Module ℂ W]
      [FiniteDimensional ℂ W],
    Module.finrank ℂ V ≤ Module.finrank ℂ W →
      nilpotentGeneratedMaxDimension l V ≤ nilpotentGeneratedMaxDimension l W) ∧
  (∀ l : ℕ, Monotone (nilpotentGeneratedPhi l))

end Langlands.Renard
