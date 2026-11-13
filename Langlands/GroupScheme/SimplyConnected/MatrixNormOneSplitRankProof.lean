import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankStatement
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankUpper
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankLower

/-!
# Split rank of special linear groups over division algebras: proof

The split rank of the actual reduced-norm-one group of `M_m(D)` is `m - 1`, over any
field. The upper bound comes from the weight idempotents of a closed split torus
(`MatrixNormOneSplitRank.splitRank_le`), the lower bound from the diagonal torus
(`sub_one_le_splitRank_normOne`).
-/

universe u

namespace Langlands.GroupScheme.CentralSimpleUnits

/-- **Split rank of `SL_m(D)`.** For a finite-dimensional central division algebra `D`
over any field `K` and a positive `m`, the split rank of the reduced-norm-one group of
`M_m(D)` is `m - 1`. -/
theorem matrixNormOneSplitRank : MatrixNormOneSplitRankStatement.{u} := by
  intro K D _ _ _ _ _ m _
  exact le_antisymm MatrixNormOneSplitRank.splitRank_le (sub_one_le_splitRank_normOne K D m)

end Langlands.GroupScheme.CentralSimpleUnits
