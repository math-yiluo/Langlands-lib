import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof

/-!
# Proof of `Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.Dynamic

/-- Proof of `LeviAdjointDeterminantReciprocityStatement`. -/
theorem leviAdjointDeterminantReciprocity : LeviAdjointDeterminantReciprocityStatement.{u} :=
  leviAdjointDeterminantReciprocity_of_structure relativeRootReflectionExistence
    centralSplitTorusCharacter dynamicCentralizerReductive

end Langlands.GroupScheme.Dynamic
