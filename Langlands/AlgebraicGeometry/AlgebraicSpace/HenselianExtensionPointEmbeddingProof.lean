import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionClosedReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteExtensionPointClosedRangeProof

/-!
# Rational points over an extension of henselian valued fields

The full extension embedding statement follows from the complete-field closed-range
theorem and the completion and separated-open reduction.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The natural map on rational points over an arbitrary henselian normed field extension
is an embedding, and a closed embedding when the base field is closed in the extension,
for quasi-separated spaces locally of finite type covered by separated open subspaces. -/
theorem henselianExtensionPointEmbedding : HenselianExtensionPointEmbeddingStatement.{u} :=
  ExtensionClosedReduction.henselianExtensionPointEmbedding_of_complete
    CompleteExtensionClosedRange.completeExtensionPointClosedRange

end Langlands.AlgebraicGeometry.AlgebraicSpace
