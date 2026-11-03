import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-! # Finite orthant coordinates modulo the kernel of the root pairings -/

namespace Langlands

open scoped BigOperators

/-- Standard cocharacters give finite translates of an orthant, modulo the
common kernel of the integral pairings. No nonempty-root assumption is made. -/
def FiniteChamberLatticeStatement.{uΔ, uX} : Prop :=
  ∀ (Δ : Type uΔ) [Fintype Δ] (X : Type uX) [AddCommGroup X]
    (pair : Δ → X →+ ℤ),
    (∀ I : Finset Δ, ∃ ζ : X,
      (∀ β ∈ I, pair β ζ = 0) ∧ ∀ β ∉ I, 0 < pair β ζ) →
    ∃ gen : Δ → X,
      (∀ α, 0 < pair α (gen α)) ∧
      (∀ α β, β ≠ α → pair β (gen α) = 0) ∧
      ∀ B : ℤ, ∃ R : Set X, R.Finite ∧
        ∀ x : X, (∀ α, -B ≤ pair α x) →
          ∃ r ∈ R, ∃ n : Δ → ℕ, ∃ z : X,
            (∀ α, pair α z = 0) ∧ x = r + (∑ α, n α • gen α) + z

end Langlands
