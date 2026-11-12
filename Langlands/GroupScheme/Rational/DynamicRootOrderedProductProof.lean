import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Ordered relative-root products onto the actual Dynamic radical -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- **Ordered relative-root products** onto the actual Dynamic radical, over
every field and at every universe, with all structural prerequisites
discharged. -/
theorem dynamicRootOrderedProduct : DynamicRootOrderedProductStatement.{u} :=
  dynamicRootOrderedProduct_of_rayDecomposition
    (relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement
      rootRankOneFactorization)

end Langlands.GroupScheme.RelativeRoot
