import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Finite chamber Cartan charts modulo the full center -/

namespace Langlands

open scoped BigOperators

/-- A lower-bounded lattice Cartan cover has finitely many orthant charts modulo
the full center. With no root labels its quotient is compact. -/
def FiniteChamberCartanCoverStatement.{uΔ, uX, uG} : Prop :=
  ∀ (Δ : Type uΔ) [Fintype Δ] (X : Type uX) [AddCommGroup X]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Set G), IsCompact K →
    ∀ (e : Multiplicative X →* G) (pair : Δ → X →+ ℤ) (F₀ : Set G),
    F₀.Finite →
    (∀ I : Finset Δ, ∃ ζ : X,
      (∀ β ∈ I, pair β ζ = 0) ∧ ∀ β ∉ I, 0 < pair β ζ) →
    (∀ z : X, (∀ α, pair α z = 0) → e (.ofAdd z) ∈ Subgroup.center G) →
    ∀ B : ℤ,
    (∀ g : G, ∃ k₁ ∈ K, ∃ x : X, ∃ f ∈ F₀, ∃ k₂ ∈ K,
      (∀ α, -B ≤ pair α x) ∧ g = k₁ * e (.ofAdd x) * f * k₂) →
    ∃ gen : Δ → X,
      (∀ α, 0 < pair α (gen α)) ∧
      (∀ α β, β ≠ α → pair β (gen α) = 0) ∧
      ∃ T : Set G, T.Finite ∧
        (∀ g : G, ∃ n : Δ → ℕ, ∃ k₁ ∈ K, ∃ t ∈ T, ∃ k₂ ∈ K,
          ∃ z ∈ Subgroup.center G,
            g = k₁ * e (.ofAdd (∑ α, n α • gen α)) * t * k₂ * z) ∧
        (IsEmpty Δ → CompactSpace (G ⧸ Subgroup.center G))

end Langlands
