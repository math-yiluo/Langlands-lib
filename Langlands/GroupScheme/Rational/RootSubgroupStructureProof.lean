import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.GroupScheme.Rational.RootSubgroupUniquenessProof
import Langlands.GroupScheme.Rational.RootSubgroupVectorProof

/-!
# Proof of `Langlands.GroupScheme.RelativeRoot.RootSubgroupStructureStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- Proof of `RootSubgroupStructureStatement`. -/
theorem rootSubgroupStructure : RootSubgroupStructureStatement.{u} :=
  ⟨characterFpqc, kernelCentralizerStructure, quotientActionComparison,
    rootSubgroupRealization, rootSubgroupUniqueness, rootSubgroupVector⟩

end Langlands.GroupScheme.RelativeRoot
