import Langlands.GroupScheme.ParabolicQuotientProperReduction
import Langlands.GroupScheme.Absolute.BorelProperQuotientProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.HomogeneousQuotientProof

/-! # Properness of homogeneous quotients by parabolic subgroups -/

universe u

namespace Langlands.GroupScheme

/-- Every actual homogeneous quotient of a connected smooth affine group over a field by a
geometrically parabolic subgroup is proper. -/
theorem parabolicSubgroupQuotientProper : ParabolicSubgroupQuotientProperStatement.{u} :=
  ParabolicQuotient.parabolicSubgroupQuotientProper_of someBorelQuotientProper borelConjugacy
    smoothSubgroupQuotientExistence

end Langlands.GroupScheme
