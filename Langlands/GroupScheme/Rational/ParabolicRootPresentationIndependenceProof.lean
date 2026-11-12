import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-!
# Proof of `Langlands.GroupScheme.ParabolicRootPresentationIndependenceStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `ParabolicRootPresentationIndependenceStatement`. -/
theorem parabolicRootPresentationIndependence : ParabolicRootPresentationIndependenceStatement.{u} :=
  parabolicRootPresentation.2.1

end Langlands.GroupScheme
