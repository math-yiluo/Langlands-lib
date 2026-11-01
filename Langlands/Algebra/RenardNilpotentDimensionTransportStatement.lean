import Langlands.Algebra.RenardNilpotentDimensionMaximum

noncomputable section

universe u v

namespace Langlands.Renard

/-- Carrier invariance and the canonical-dimension interpretation of Renard's maximum. -/
def NilpotentDimensionTransportStatement : Prop :=
  (∀ (l : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
      [FiniteDimensional ℂ V] (W : Type v) [AddCommGroup W] [Module ℂ W]
      [FiniteDimensional ℂ W] (_e : V ≃ₗ[ℂ] W),
    nilpotentGeneratedDimensions l V = nilpotentGeneratedDimensions l W ∧
      nilpotentGeneratedMaxDimension l V = nilpotentGeneratedMaxDimension l W) ∧
  (∀ (l : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
      [FiniteDimensional ℂ V],
    nilpotentGeneratedMaxDimension l V =
      nilpotentGeneratedPhi l (Module.finrank ℂ V))

end Langlands.Renard
