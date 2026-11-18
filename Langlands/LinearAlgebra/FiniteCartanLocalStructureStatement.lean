import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Local restrictions on finite Cartan matrices -/

universe u v

open Matrix

namespace Langlands.LinearAlgebra

/-- Internal local consequences used by the finite Cartan enumeration. -/
def FiniteCartanLocalStructureStatement : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
    M.IsFiniteCartan →
      (∀ (κ : Type v) [Fintype κ] [DecidableEq κ] (f : κ → ι),
        Function.Injective f → (M.submatrix f f).IsFiniteCartan) ∧
      (∀ x : ι → ℤ, (∀ i, 0 ≤ x i) → x ≠ 0 →
        ∃ i, 0 < x i ∧ 0 < (M *ᵥ x) i) ∧
      (∀ i j, i ≠ j →
        (M i j = 0 ∧ M j i = 0) ∨
        (M i j = -1 ∧ M j i = -1) ∨
        (M i j = -1 ∧ M j i = -2) ∨
        (M i j = -2 ∧ M j i = -1) ∨
        (M i j = -1 ∧ M j i = -3) ∨
        (M i j = -3 ∧ M j i = -1)) ∧
      (∀ i, ∑ j ∈ Finset.univ.erase i, M i j * M j i ≤ 3)

end Langlands.LinearAlgebra
