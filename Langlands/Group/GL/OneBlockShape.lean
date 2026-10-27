import Langlands.Group.GL.Blocks

/-! The positive single-block shape, shared by Levi refinements. -/

namespace Langlands.CuspidalSupport.LeviAdmissibility

open GeneralLinear

/-- The block shape of rank `m` with a single block. -/
def oneBlock (m : ℕ) (hm : 0 < m) : BlockShape m where
  length := 1
  size := fun _ => m
  positive := fun _ => hm
  sum_eq := by simp

end Langlands.CuspidalSupport.LeviAdmissibility
