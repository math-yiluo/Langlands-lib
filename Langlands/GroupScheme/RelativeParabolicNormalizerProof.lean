import Langlands.GroupScheme.RelativeParabolicNormalizerStatement
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.RelativeSelfNormalizerProof
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Parabolic subgroups of reductive group schemes are self-normalizing: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Parabolic subgroups are self-normalizing over any ring** (Conrad, *Reductive group
schemes* (2014), Corollary 5.2.8, first assertion). The published reduction
`RelativeParabolicNormalizerReduction.normalizer_eq_of_statements` is applied to the
published proofs of its three proposition inputs. -/
theorem relativeParabolicSelfNormalizer : RelativeParabolicSelfNormalizerStatement.{u} :=
  fun _ _ _ _ _ hG hPsmooth hi hP =>
    RelativeParabolicNormalizerReduction.normalizer_eq_of_statements
      relativeSelfNormalizer parabolicSelfNormalizer parabolicDynamic hG hPsmooth hi hP

end Langlands.GroupScheme
