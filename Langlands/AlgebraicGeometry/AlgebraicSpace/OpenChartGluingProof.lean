import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing

/-! # Scheme representability from locally surjective open charts -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Gluing represented open charts constructs a scheme over the original base. -/
theorem openChartGluing : OpenChartGluingStatement.{u} := by
  intro S F I U a ha hcover
  let := hcover
  exact SliceOpenGluing.exists_representation (G := F) ha

end Langlands.AlgebraicGeometry.AlgebraicSpace
