import Langlands.GroupScheme.Rational.ParabolicIntersectionAssembly
import Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof

/-!
# Proof of `Langlands.GroupScheme.ParabolicIntersectionSplitTorusStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `ParabolicIntersectionSplitTorusStatement`. -/
theorem parabolicIntersectionSplitTorus : ParabolicIntersectionSplitTorusStatement.{u} :=
  parabolicIntersectionSplitTorusStatement_of_centralizer parabolicIntersectionCentralizer

end Langlands.GroupScheme
