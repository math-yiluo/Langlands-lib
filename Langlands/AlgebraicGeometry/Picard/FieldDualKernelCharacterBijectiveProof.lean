import Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveStatement
import Langlands.AlgebraicGeometry.Picard.DualKernelClassComparison
import Langlands.AlgebraicGeometry.Picard.FieldTrivialPullbackPicardZeroProof
import Langlands.AbelianScheme.FieldTrivialPullbackCharacterBijective

/-! # Bijectivity of the actual dual-kernel character over a field -/

universe u

namespace Langlands.AbelianScheme

/-- The existing normalized dual-kernel character is bijective on every test
scheme over an arbitrary field, with exactly its existing constructor inputs. -/
theorem fieldDualKernelCharacterBijective :
    FieldDualKernelCharacterBijectiveStatement.{u} := by
  intro preservation composition unitCoherence associativity comparison symmetry stability
    k _ A B hA hB MA evaluationA MB evaluationB f hf T
  exact dualKernelPointCharacter_bijective_of_classification f hA stability hB
    preservation composition unitCoherence associativity comparison symmetry
    MA evaluationA MB evaluationB T
    (fieldTrivialPullbackPicardZero k A B f hf T)
    (fieldTrivialPullbackCharacterBijective k A B f hf T)

end Langlands.AbelianScheme
