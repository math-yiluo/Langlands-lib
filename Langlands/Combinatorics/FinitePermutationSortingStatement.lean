import Mathlib.Data.Fintype.Perm
import Mathlib.Basic.Real.Basic

/-! # Finite sorting by adjacent strict inversions

An internal proposition separating finite permutation sorting from the
representation-theoretic arguments that preserve a chosen invariant.
-/

namespace Langlands.Combinatorics

/-- Any invariant of finite permutations that holds initially and survives
swapping an adjacent strict inversion admits a weakly decreasing arrangement.
The permutation sends a new position to its original label. -/
def FinitePermutationSorting : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (P : Equiv.Perm (Fin n) → Prop),
    P (Equiv.refl _) →
    (∀ (σ : Equiv.Perm (Fin n)), P σ →
      ∀ (j : ℕ) (h : j + 1 < n),
        x (σ ⟨j, by omega⟩) < x (σ ⟨j + 1, h⟩) →
          P ((Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩).trans σ)) →
    ∃ σ : Equiv.Perm (Fin n), P σ ∧ Antitone (fun i => x (σ i))

end Langlands.Combinatorics
