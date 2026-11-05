import Langlands.GroupScheme.Rational.UnipotentWoundCriterionFromVectorFactor
import Langlands.GroupScheme.Rational.CommutativePTorsionVectorFactorProof

/-! # The central additive-subgroup criterion over every field -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected affine unipotent group has only constant affine-line
maps exactly when it has no central closed one-dimensional vector subgroup. -/
theorem unipotentWoundCriterion : UnipotentWoundCriterionStatement.{u} :=
  UnipotentWoundCriterionReduction.criterion_of_vectorFactor
    RelativeRoot.commutativePTorsionVectorFactor

end Langlands.GroupScheme
