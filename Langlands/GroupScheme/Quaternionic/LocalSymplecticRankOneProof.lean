import Langlands.GroupScheme.Quaternionic.LocalSymplecticRankOneStatement
import Langlands.GroupScheme.Quaternionic.SymplecticSplitRank
import Langlands.GroupScheme.SymplecticMatrix.StandardComparison
import Langlands.GroupScheme.Symplectic.StructureProof
import Langlands.LocalField.ValuativeInfinite

/-! # Quaternionic symplectic groups of rank one over local fields -/

noncomputable section

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- The symplectic group of a nondegenerate trace-valued antihermitian form
of rank two or three and Witt index one over a quaternion division algebra
over a nonarchimedean local field is simply connected, almost simple and
of split rank one, in every characteristic. -/
theorem localSymplecticRankOne : LocalSymplecticRankOneStatement.{u} := by
  intro K _ _ _ _ D _ _ _ _ hD σ hS m _ hm H hH hu hw
  let : Infinite K := Langlands.LocalField.infinite_of_isNonarchimedeanLocalField K
  obtain ⟨M⟩ := FirstKindInvolution.nonempty_algebraicModel hD σ hS H hH hu
  have hn : 2 ≤ Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using
      (show 2 ≤ m from hm.elim (fun h => by omega) (fun h => by omega))
  obtain ⟨hsc, has⟩ :=
    M.isSimplyConnected_and_isAlmostSimple Symplectic.structureStatement hn
  exact ⟨hsc, has,
    σ.splitRank_symplecticGroup_eq_one_of_wittIndex_eq_one hm H hH hu hw⟩

end Langlands.GroupScheme.Quaternionic
