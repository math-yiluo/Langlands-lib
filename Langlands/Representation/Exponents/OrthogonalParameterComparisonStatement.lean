import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Orthogonal parameter comparison

An internal real inner-product statement isolating the elementary comparison
step in parameter uniqueness. It makes no representation-theoretic assertion.
-/

namespace Langlands.Exponents

universe u

/-- Equal differences of two orthogonal pairs with nonnegative cross pairings
force equality of both members of the pairs. -/
def OrthogonalParameterComparisonStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x₁ y₁ x₂ y₂ : E),
    x₁ - y₁ = x₂ - y₂ →
    inner ℝ x₁ y₁ = 0 → inner ℝ x₂ y₂ = 0 →
    0 ≤ inner ℝ x₁ y₂ → 0 ≤ inner ℝ y₁ x₂ →
      x₁ = x₂ ∧ y₁ = y₂

end Langlands.Exponents
