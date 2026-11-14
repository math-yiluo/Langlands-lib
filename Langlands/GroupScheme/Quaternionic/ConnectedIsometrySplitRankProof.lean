import Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankStatement
import Langlands.GroupScheme.Quaternionic.QuadraticTorusWittBound
import Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicSplitTorus

/-!
# Split rank of `O(q)⁰` equals the Witt index

Over every field, the split rank of the identity component `O(q)⁰` of the isometry group of a
nondegenerate `σ`-quadratic form `q` equals the Witt index of `q`.

The upper bound `splitRank O(q)⁰ ≤ quadraticWittIndex q` is
`QuadraticTorusWittBound.splitRank_connectedIsometryGroup_le`; the lower bound
`quadraticWittIndex q ≤ splitRank O(q)⁰` is
`FirstKindInvolution.quadraticWittIndex_le_splitRank_connectedIsometryGroup`.
-/

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- **Split rank of `O(q)⁰`.** For a nondegenerate `σ`-quadratic form `q` with smooth isometry
group, the split rank of `O(q)⁰` is the Witt index of `q`, over every field. -/
theorem connectedIsometrySplitRank : ConnectedIsometrySplitRankStatement.{u} := by
  intro K D _ _ _ _ _ degree _ σ _ n _ _ q _ hq
  exact le_antisymm (QuadraticTorusWittBound.splitRank_connectedIsometryGroup_le σ q)
    (FirstKindInvolution.quadraticWittIndex_le_splitRank_connectedIsometryGroup q hq)

end Langlands.GroupScheme.Quaternionic
