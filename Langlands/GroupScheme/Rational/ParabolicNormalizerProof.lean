import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement
import Langlands.GroupScheme.Rational.ParabolicNormalizerDescent
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelNormalizerProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Parabolic subgroups are self-normalizing on all tests: proof -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Over every field, a parabolic subgroup of a connected reductive group is its own
normalizer, as subgroup functors on all test schemes. -/
theorem parabolicSelfNormalizer : ParabolicSelfNormalizerStatement.{u} :=
  parabolicSelfNormalizerStatement_of_rational_descent borelConjugacy borelNormalizer
    parabolicDynamic dynamicConnected

end Langlands.GroupScheme
