import Langlands.GroupScheme.UnipotentClosedSubgroupAssembly
import Langlands.GroupScheme.UnipotentMatrixCriterion.Criterion
import Langlands.GroupScheme.CoalgebraUnipotence.CriterionProof

universe u

namespace Langlands.GroupScheme

/-- Closed subgroups of affine unipotent group schemes over a field are unipotent. -/
theorem unipotentClosedSubgroup : UnipotentClosedSubgroupStatement.{u} :=
  unipotentClosedSubgroup_of_matrixCriteria
    UnipotentMatrixCriterion.corepresentedMatrixUnipotence
    CoalgebraUnipotence.matrixUnipotenceConilpotence
    CoalgebraUnipotence.conilpotenceQuotient

end Langlands.GroupScheme
