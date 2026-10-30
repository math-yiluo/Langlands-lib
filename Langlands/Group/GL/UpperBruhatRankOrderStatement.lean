import Langlands.Group.GL.UpperBruhatFiltration
import Langlands.Group.GL.UpperBruhatRankProof

/-! Strict inversion growth for permutations ordered by their lower-left corner counts. -/

namespace Langlands.GeneralLinear

/-- In every rank `n`, including zero, if two distinct permutations `v ≠ w` of `Fin n`
satisfy `UpperBruhatRank.count v i j.val ≤ UpperBruhatRank.count w i j.val` for all
`i j : Fin (n + 1)`, then `v` has strictly fewer inversions than `w`. The count is the
number of columns `c` with `c.val < j.val` and `i.val ≤ (w c).val`. -/
def UpperBruhatRankOrderInversionStatement : Prop :=
  ∀ (n : ℕ) (v w : Equiv.Perm (Fin n)), v ≠ w →
    (∀ i j : Fin (n + 1),
      UpperBruhatRank.count v i j.val ≤ UpperBruhatRank.count w i j.val) →
    permutationInversionCount n v < permutationInversionCount n w

end Langlands.GeneralLinear
