import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Exact classification of nonempty indecomposable finite Cartan matrices -/

universe u

namespace Langlands.LinearAlgebra

namespace FiniteCartanMatrix

variable {ι : Type u} (M : Matrix ι ι ℤ)

/-- An exact numbering of the entire index type of an integral matrix. -/
def HasCartanMatrix {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ e : ι ≃ Fin n, ∀ i j, M i j = N (e i) (e j)

/-- The nine finite irreducible Cartan families, with exact ordered entries. -/
def HasIrreducibleCartanType : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ HasCartanMatrix M (CartanMatrix.A n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ HasCartanMatrix M (CartanMatrix.B n)) ∨
  (∃ n : ℕ, 2 ≤ n ∧ HasCartanMatrix M (CartanMatrix.C n)) ∨
  (∃ n : ℕ, 4 ≤ n ∧ HasCartanMatrix M (CartanMatrix.D n)) ∨
  HasCartanMatrix M (CartanMatrix.E 6) ∨
  HasCartanMatrix M (CartanMatrix.E 7) ∨
  HasCartanMatrix M (CartanMatrix.E 8) ∨
  HasCartanMatrix M CartanMatrix.F₄ ∨
  HasCartanMatrix M CartanMatrix.G₂

end FiniteCartanMatrix

/-- Every nonempty indecomposable finite Cartan matrix has an exact numbering
by one of the nine finite irreducible families. This proposition is a target;
the present module does not prove the classification. -/
def FiniteCartanClassificationStatement : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℤ), M.IsFiniteCartan → M.IsIndecomposable →
      FiniteCartanMatrix.HasIrreducibleCartanType M

end Langlands.LinearAlgebra
