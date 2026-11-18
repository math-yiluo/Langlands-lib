import Langlands.Algebra.CentralSimple.CentralDivisionTensorCubeStatement
import Langlands.Algebra.CentralDivisionTensorCubeNonSplit

/-! # Exact degree-six tensor-cube nonsplitting target -/

noncomputable section
universe u

namespace Langlands.CentralSimple

/-- The exact published positive-size tensor-cube nonsplitting statement. -/
theorem centralDivisionDegreeSixTensorCubeNonSplit :
    CentralDivisionDegreeSixTensorCubeNonSplitStatement.{u} := by
  intro k _ D _ _ _ _ hdim n _
  exact centralDivision_degree_six_tensorCube_not_split hdim n

end Langlands.CentralSimple
