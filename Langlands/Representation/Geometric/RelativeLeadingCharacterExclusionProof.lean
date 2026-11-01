import Langlands.Representation.Geometric.RelativeLeadingCharacterExclusionStatement
import Langlands.Representation.Geometric.GeometricPieceTemperedExclusion

/-! Actual leading-character exclusion in reversed geometric pieces. -/

namespace Langlands

universe uF uV

set_option maxHeartbeats 1600000 in
/-- The leading coarse real character in an actual reversed geometric piece
forces its raw minimal representative to be inverse block reversal. -/
theorem relativeGeometricLeadingCharacterExclusion :
    GLRelativeGeometricLeadingCharacterExclusionStatement.{uF, uV} := by
  intro p _ F T n B
  exact Geometric.geometricPiece_tempered_leading_implies_reverse T B

end Langlands
