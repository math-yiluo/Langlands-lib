import Langlands.GroupScheme.Rational.CommutativePTorsionVectorFactorProof
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionFromVectorFactor
import Langlands.GroupScheme.Rational.WoundSeparableFromCriterion

/-! # Woundness under separable algebraic field extension -/

universe u

namespace Langlands.GroupScheme

/-- Affine-line constancy of a smooth connected affine unipotent group is
invariant under every separable algebraic field extension. -/
theorem unipotentWoundSeparableExtension :
    UnipotentWoundSeparableExtensionStatement.{u} :=
  woundSeparableFromCriterion
    (UnipotentWoundCriterionReduction.criterion_of_vectorFactor
      RelativeRoot.commutativePTorsionVectorFactor)

end Langlands.GroupScheme
