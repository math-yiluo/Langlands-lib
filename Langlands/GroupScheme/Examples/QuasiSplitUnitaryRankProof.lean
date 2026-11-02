import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryCocharacterClosed
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankBound
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus

noncomputable section
universe u

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- The quasi-split unitary group has split rank one over F and contains a split torus
of rank two after base change to E. -/
theorem rankStatement : RankStatement.{u} := by
  classical
  intro F E _ _ _ _ κ _ b c hc
  refine ⟨isClosedSubgroup_cocharacter b c, ?_, exists_rankTwo_splitTorus b c hc⟩
  intro I _ i hi
  let := Fintype.ofFinite I
  exact splitTorus_rank_le_one b c I i hi

end Langlands.GroupScheme.QuasiSplitUnitary
