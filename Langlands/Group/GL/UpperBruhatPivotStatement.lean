import Langlands.Group.GL.Basic
import Langlands.Group.GL.Maps

/-! Ordered pivot isolation for upper triangular Bruhat induction. -/

namespace Langlands.GeneralLinear

universe u

/-- Upper triangular operations isolate a unit pivot in the last row and leave
an invertible minor with its remaining columns in their original order. -/
def FieldUpperBruhatPivotTheorem : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (g : GeneralLinear (n + 1) K),
    ∃ (L R : GeneralLinear (n + 1) K) (p : Fin (n + 1)) (h : GeneralLinear n K),
      (∀ i j : Fin (n + 1), j < i → L i j = 0) ∧
      (∀ i j : Fin (n + 1), j < i → R i j = 0) ∧
      (∀ j : Fin (n + 1), (L * g * R) (Fin.last n) j = if j = p then 1 else 0) ∧
      (∀ i : Fin n, (L * g * R) i.castSucc p = 0) ∧
      (∀ i j : Fin n, (L * g * R) i.castSucc (p.succAbove j) = h i j)

end Langlands.GeneralLinear
