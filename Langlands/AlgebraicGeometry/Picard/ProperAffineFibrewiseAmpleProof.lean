import Langlands.AlgebraicGeometry.Picard.ProperAffineFibrewiseAmpleStatement
import Langlands.AlgebraicGeometry.Picard.AffineBaseAmpleLocality

/-! # Fibrewise ampleness over a noetherian affine base -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- A specified fibrewise ample bundle is ample on a proper family over
a locally noetherian affine base. -/
theorem properAffineFibrewiseAmple : ProperAffineFibrewiseAmpleStatement.{u} := by
  intro X S _ _ f _ L hL
  exact L.isAmple_of_fibrewise_over_affine f hL

end Langlands.AlgebraicGeometry.Picard
