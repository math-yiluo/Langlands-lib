import Langlands.GroupScheme.AffineNormalSubgroupQuotientEquivalence
import Langlands.GroupScheme.NormalQuotientExistenceProof

/-! # Affine quotients by normal closed subgroups -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem affineNormalSubgroupQuotient :
    AffineNormalSubgroupQuotientStatement.{u} :=
  NormalSubgroupQuotientExistenceStatement.toAffineNormalSubgroupQuotientStatement
    normalSubgroupQuotientExistence

end Langlands.GroupScheme
