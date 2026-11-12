import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # dynamicUnipotentUnipotence: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Every actual representative of the dynamic unipotent subgroup of an affine locally finite-type field group is unipotent in the published representation-theoretic sense. -/
theorem dynamicUnipotentUnipotence :
    DynamicUnipotentUnipotenceStatement.{u} :=
  dynamicUnipotentUnipotenceReduction unitriangularUnipotent unipotentClosedSubgroup

end Langlands.GroupScheme
