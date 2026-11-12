import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-!
# Proof of `Langlands.GroupScheme.ParabolicRootPresentationIsoStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `ParabolicRootPresentationIsoStatement`. -/
theorem parabolicRootPresentationIso : ParabolicRootPresentationIsoStatement.{u} :=
  parabolicRootPresentation.2.2

end Langlands.GroupScheme
