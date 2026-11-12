import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.RootRayDecompositionProof
import Langlands.GroupScheme.Rational.SemigroupOrderedProductProof

/-!
# Proof of `Langlands.GroupScheme.RelativeRoot.RootProductStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- Proof of `RootProductStatement`. -/
theorem rootProduct : RootProductStatement.{u} :=
  ⟨semigroupOrderedProduct, relativeRootRayDecomposition, dynamicRootOrderedProduct⟩

end Langlands.GroupScheme.RelativeRoot
