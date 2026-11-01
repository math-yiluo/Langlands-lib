import Langlands.Algebra.RenardNilpotentDimensionMaximum

noncomputable section

universe u

namespace Langlands.Renard

/-- The source base cases for the actual nilpotent maximum, with the zero and
empty-generator conventions made explicit on arbitrary and canonical carriers. -/
def NilpotentDimensionBaseCasesStatement : Prop :=
  (∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    (∀ l : ℕ, Module.finrank ℂ V = 0 →
      nilpotentGeneratedMaxDimension l V = 0) ∧
    (∀ l : ℕ, Module.finrank ℂ V = 1 →
      nilpotentGeneratedMaxDimension l V = 1) ∧
    nilpotentGeneratedMaxDimension 1 V ≤ Module.finrank ℂ V ∧
    nilpotentGeneratedMaxDimension 0 V =
      if Module.finrank ℂ V = 0 then 0 else 1) ∧
  (∀ l : ℕ, nilpotentGeneratedPhi l 0 = 0) ∧
  (∀ l : ℕ, nilpotentGeneratedPhi l 1 = 1) ∧
  (∀ k : ℕ, nilpotentGeneratedPhi 1 k ≤ k) ∧
  (∀ k : ℕ, nilpotentGeneratedPhi 0 k = if k = 0 then 0 else 1)

end Langlands.Renard
