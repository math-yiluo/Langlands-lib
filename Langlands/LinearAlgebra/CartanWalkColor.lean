import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # Cartan invariants from adjacency walk counts -/

namespace Langlands.CartanWalkColor

variable {n : ℕ}

/-- Sum the colors at the vertices joined to a given vertex by a Cartan
entry equal to minus one. -/
def step (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℕ) : Fin n → ℕ :=
  fun i => ∑ j, if M i j = -1 then c j else 0

/-- An entry-preserving bijection preserves each refinement of an invariant
vertex coloring. -/
theorem step_invariant {M : Matrix (Fin n) (Fin n) ℤ}
    {f : Fin n → Fin n} (hf : ∀ i j, M (f i) (f j) = M i j)
    (hbij : Function.Bijective f) {c : Fin n → ℕ}
    (hc : ∀ i, c (f i) = c i) :
    ∀ i, step M c (f i) = step M c i := by
  intro i
  exact (Fintype.sum_bijective f hbij
    (fun j => if M i j = -1 then c j else 0)
    (fun j => if M (f i) j = -1 then c j else 0)
    (fun j => by rw [hf, hc])).symm

end Langlands.CartanWalkColor
