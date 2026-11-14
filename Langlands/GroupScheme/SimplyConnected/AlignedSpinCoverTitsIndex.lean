import Langlands.GroupScheme.SimplyConnected.AlignedSpinCoverTitsIndexReduction
import Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankProof
import Langlands.GroupScheme.Quaternionic.MaximalSplitTorusWeightsProof
import Langlands.GroupScheme.Quaternionic.SpinCoverVectorInputs
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationProof
import Langlands.GroupScheme.OrthogonalMatrix.NumberedCoverVectorProof

/-!
# Index comparisons for an aligned type-D spin cover

This file proves `Langlands.GroupScheme.AlignedSpinCoverTitsIndexStatement` by supplying the
three prerequisite results to the reduction `alignedSpinCoverTitsIndex_of_weights`.
-/

universe u

namespace Langlands.GroupScheme

/-- For an aligned type-D spin cover `π : G ⟶ O(q)` of a simply connected absolutely almost
simple group, the Witt index of `q` equals the split rank of `G`, and a vertex `a` with
`(e a).val + 2 < n` is distinguished exactly when `(e a).val + 1` is a positive multiple
`j * degree` with `j` at most the Witt index. -/
theorem alignedSpinCoverTitsIndex : AlignedSpinCoverTitsIndexStatement.{u} :=
  alignedSpinCoverTitsIndex_of_weights Quaternionic.connectedIsometrySplitRank
    Quaternionic.isometryMaximalSplitTorusWeights
    (spinCoverVectorWeights_of_representation_inputs
      Quaternionic.orthogonalMoritaRepresentation
      OrthogonalMatrix.numberedCoverVector)

end Langlands.GroupScheme
