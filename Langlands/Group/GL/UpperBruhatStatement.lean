import Langlands.Group.GL.Basic
import Langlands.Group.GL.Maps

/-! Upper triangular Bruhat factorization over an arbitrary field. -/

namespace Langlands.GeneralLinear

universe u

/-- Every invertible matrix over a field factors as an upper triangular matrix,
a permutation matrix, and an upper triangular matrix, including in rank zero. -/
def FieldUpperBruhatFactorizationTheorem : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (g : GeneralLinear n K),
    ∃ (a b : GeneralLinear n K) (w : Equiv.Perm (Fin n)),
      (∀ i j : Fin n, j < i → a i j = 0) ∧
      (∀ i j : Fin n, j < i → b i j = 0) ∧
      g = a * permutation n K w * b

end Langlands.GeneralLinear
