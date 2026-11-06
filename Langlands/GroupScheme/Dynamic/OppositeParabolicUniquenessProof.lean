import Langlands.GroupScheme.Dynamic.OppositeParabolicComparison
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Uniqueness of the opposite dynamic parabolic: proof -/

universe u

namespace Langlands.GroupScheme

/-- Equal dynamic centralizers and opposition on rational points determine the
opposite dynamic parabolic and its unipotent subgroup over every field. -/
theorem oppositeDynamicParabolicUniqueness :
    OppositeDynamicParabolicUniquenessStatement.{u} :=
  oppositeDynamicParabolicUniqueness_of_relativeRootNegation relativeRootNegation

end Langlands.GroupScheme
