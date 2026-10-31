import Langlands.Group.GL.Blocks
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! The positive two-block shape with a prescribed cut, shared by Levi refinements. -/

namespace Langlands.ProductLeviChamber

open GeneralLinear

/-- The block shape `(k, N - k)` of `N`. -/
def twoBlock (N k : ℕ) (hk : 0 < k) (hkN : k < N) : BlockShape N where
  length := 2
  size := ![k, N - k]
  positive := by
    intro i
    fin_cases i
    · exact hk
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  sum_eq := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega

theorem twoBlock_index_val (N k : ℕ) (hk : 0 < k) (hkN : k < N)
    (i : Fin (twoBlock N k hk hkN).length) (r : Fin ((twoBlock N k hk hkN).size i)) :
    ((twoBlock N k hk hkN).index i r : ℕ) = (if i.val = 0 then 0 else k) + r := by
  change ((finSigmaFinEquiv.trans (finCongr (twoBlock N k hk hkN).sum_eq)) ⟨i, r⟩ : ℕ) = _
  rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  have hi : i.val < 2 := i.isLt
  rcases i with ⟨i, hi'⟩
  interval_cases i
  · simp
  · simp [twoBlock]

end Langlands.ProductLeviChamber
