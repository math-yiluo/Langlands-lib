import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.RelativeRealSimpleRootBasisProof
import Langlands.GroupScheme.Rational.RelativeRealCorootProof
import Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof

/-!
# Renard V.3.7, V.3.12 and V.3.13: the assembled real coroot linear algebra

The conjunction `RelativeRealCorootLinearAlgebraStatement` is proved by pairing the four
published component proofs. See the paired Markdown file.
-/

universe u

namespace Langlands.GroupScheme

/-- Renard V.3.7, V.3.12 (real form) and V.3.13 (corrected): the conjunction of the four
published component theorems. -/
theorem relativeRealCorootLinearAlgebra :
    RelativeRealCorootLinearAlgebraStatement.{u} :=
  ⟨relativeRealSimpleRootBasis, relativeRealCoroot, relativeFundamentalWeight,
    standardLeviRealDecomposition⟩

end Langlands.GroupScheme
