import Langlands.GroupScheme.Rational.StandardSourceTwistedIntersectionReduction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof

/-! # Standard source parabolics and radicals for minimum geometric terms: proof -/

universe u

namespace Langlands.GroupScheme

/-- For every minimum double-coset representative and every scheme-normalizer
lift, the source parabolic and radical inside the standard Levi are the literal
standard parabolic and radical of the intersection subset, on all test schemes. -/
theorem standardSourceTwistedIntersection :
    StandardSourceTwistedIntersectionStatement.{u} :=
  standardSourceTwistedIntersectionStatement_of_negation_of_signs
    relativeRootNegation relativeRootSignsDetermineDynamic

end Langlands.GroupScheme
