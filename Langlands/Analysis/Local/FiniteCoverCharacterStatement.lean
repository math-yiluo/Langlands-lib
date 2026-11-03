import Mathlib.Analysis.Normed.Order.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Positive characters and finite product covers -/

universe u

open scoped NNReal

namespace Langlands.Haar

/-- A positive character trivial on the two compact factors and the torus
factor of a finite product cover is trivial everywhere. This is an internal
algebraic reduction, with no assertion that such a cover exists. -/
def FiniteCoverCharacterStatement : Prop :=
  ∀ (G : Type u) [Group G] (χ : G →* ℝ≥0) (K : Subgroup G) (A E : Set G),
    E.Finite →
    (∀ k ∈ K, χ k = 1) →
    (∀ a ∈ A, χ a = 1) →
    (∀ g : G, ∃ k₁ ∈ K, ∃ a ∈ A, ∃ e ∈ E, ∃ k₂ ∈ K,
      g = k₁ * a * e * k₂) →
    ∀ g : G, χ g = 1

end Langlands.Haar
