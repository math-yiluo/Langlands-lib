import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Absolute.CentralizerUnipotentBorelContainmentReduction
import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof

/-! # Normal unipotent subgroups of cocharacter centralizers lie in ambient Borels -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- A smooth connected normal unipotent closed subgroup of a represented cocharacter
centralizer lies in every ambient Borel subgroup containing the cocharacter. -/
theorem centralizerUnipotentBorelContainment :
    CentralizerUnipotentBorelContainmentStatement.{u} :=
  centralizerUnipotentBorelContainment_of_statements centralizerBorelIntersection
    normalUnipotentBorelContainment

end Langlands.GroupScheme
