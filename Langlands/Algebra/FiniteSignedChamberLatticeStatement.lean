import Langlands.Algebra.FiniteChamberLatticeStatement
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Finite chamber charts retaining the full lattice kernel -/

namespace Langlands

open scoped BigOperators

/-- Finite independent weakly positive charts cover a chamber in a finite
torsion-free integral lattice, including its full common pairing kernel. -/
def FiniteSignedChamberLatticeStatement.{uΔ, uX} : Prop :=
  ∀ (Δ : Type uΔ) [Fintype Δ] (X : Type uX) [AddCommGroup X]
    [Module.Finite ℤ X] [Module.IsTorsionFree ℤ X]
    (pair : Δ → X →+ ℤ),
    (∀ I : Finset Δ, ∃ ζ : X,
      (∀ β ∈ I, pair β ζ = 0) ∧ ∀ β ∉ I, 0 < pair β ζ) →
    ∃ (k : ℕ) (gen : (Fin k → Bool) → (Δ ⊕ Fin k) → X),
      (∀ ε, LinearIndependent ℤ (gen ε)) ∧
      (∀ ε j α, 0 ≤ pair α (gen ε j)) ∧
      ∀ B : ℤ, ∃ R : Set X, R.Finite ∧
        ∀ x : X, (∀ α, -B ≤ pair α x) →
          ∃ r ∈ R, ∃ ε : Fin k → Bool, ∃ n : (Δ ⊕ Fin k) → ℕ,
            x = r + ∑ j, n j • gen ε j

end Langlands
