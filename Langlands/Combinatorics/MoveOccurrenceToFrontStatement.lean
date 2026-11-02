import Mathlib.GroupTheory.Perm.Fin

/-! # Moving an original occurrence to the front -/

namespace Langlands.Combinatorics

/-- A property stable under permitted adjacent swaps can move one specified
original occurrence past all its predecessors. Permutations send new positions
to original labels, so coincident values never identify occurrences. -/
def MoveOccurrenceToFront : Prop :=
  ∀ (r : ℕ) (P : Equiv.Perm (Fin r) → Prop) (R : Fin r → Fin r → Prop),
    P 1 →
    (∀ (e : Equiv.Perm (Fin r)) (j : ℕ) (hj : j + 1 < r),
      R (e ⟨j, by omega⟩) (e ⟨j + 1, hj⟩) →
      P e →
      P (e * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩)) →
    ∀ i : Fin r, (∀ j : Fin r, j < i → R j i) →
      P (Fin.cycleRange i).symm

end Langlands.Combinatorics
