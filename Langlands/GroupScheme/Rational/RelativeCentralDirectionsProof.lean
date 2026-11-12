import Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeSplitCentralDirectionsProof

/-!
# Proof of `Langlands.GroupScheme.RelativeCentralDirectionsStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `RelativeCentralDirectionsStatement`. -/
theorem relativeCentralDirections : RelativeCentralDirectionsStatement.{u} :=
  ⟨relativeCharacterRootComplement, relativeSplitCentralDirections⟩

end Langlands.GroupScheme
