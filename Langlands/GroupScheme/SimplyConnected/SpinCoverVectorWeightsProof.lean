import Langlands.GroupScheme.Quaternionic.SpinCoverVectorInputs
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationProof
import Langlands.GroupScheme.OrthogonalMatrix.NumberedCoverVectorProof

/-! # Vector weights of an aligned type-D spin cover -/

universe u

namespace Langlands.GroupScheme

/-- The numbered vector characters and their original division-algebra weight
multiplicities for an aligned type-D spin cover. -/
theorem spinCoverVectorWeights : SpinCoverVectorWeightsStatement.{u} :=
  spinCoverVectorWeights_of_representation_inputs
    Quaternionic.orthogonalMoritaRepresentation.{u}
    OrthogonalMatrix.numberedCoverVector.{u}

end Langlands.GroupScheme
