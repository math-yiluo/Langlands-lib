import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorReduction
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof

/-! # Central stable vector subgroups of split unipotent groups -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- A nontrivial smooth connected split unipotent group has a positive-dimensional
central vector subgroup stable under an action of any smooth affine group. -/
theorem splitUnipotentStableVectorSubgroup :
    SplitUnipotentStableVectorSubgroupStatement.{u} :=
  splitUnipotentStableVectorSubgroup_of_perfectFieldUnipotentSplit
    perfectFieldUnipotentSplit

end Langlands.GroupScheme.RelativeRoot
