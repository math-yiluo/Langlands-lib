import Langlands.Weil.Representation.IsomorphismInvarianceProof
import Langlands.Weil.Representation.RankDeterminantProof
import Langlands.Weil.Representation.ExactSequenceProof
import Langlands.Weil.Representation.OperationClosureProof
import Langlands.Weil.Representation.CharacterNormalizationProof

/-!
# The complete representation operation target

The published aggregate is the conjunction of its five published components.
-/

namespace Langlands.Weil

universe uG uV uU uT

/-- The complete operation, invariance and normalization target, assembled
from the five published component theorems in the order of the conjunction. -/
theorem representationOperations :
    RepresentationOperations.{uG, uV, uU, uT} :=
  ⟨representationIsomorphismInvariance.{uG, uV, uU},
    representationRankDeterminant.{uG, uV, uU},
    representationExactSequenceInvariants.{uG, uV, uU, uT},
    representationOperationClosure.{uG, uV, uU},
    representationCharacterNormalization.{uG, uV}⟩

end Langlands.Weil
