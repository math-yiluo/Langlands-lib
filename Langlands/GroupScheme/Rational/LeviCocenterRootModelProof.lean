import Langlands.GroupScheme.Rational.LeviCocenterRootModelReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityProof
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionProof

/-! # The actual based-root and character model of a Levi cocenter -/

set_option autoImplicit false

universe u

namespace Langlands.GroupScheme

/-- Every split-torus centralizer cocenter over an arbitrary field has the actual
based-root and character model of `SplitTorusCentralizerCocenterRootModelStatement`. -/
theorem splitTorusCentralizerCocenterRootModel :
    SplitTorusCentralizerCocenterRootModelStatement.{u} :=
  splitTorusCentralizerCocenterRootModel_of_rootDatum_product_intersection
    rootDatumExistence derivedMaximalTorusProductSurjectivity
    derivedMaximalTorusIntersection

end Langlands.GroupScheme
