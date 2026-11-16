import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceReduction
import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasProof

/-! # The proper-field Picard sheaf is an algebraic space -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For every proper scheme over every field, the actual fppf Picard class sheaf is
an algebraic space with closed-immersion diagonal and a surjective etale atlas
locally of finite type over the field. -/
theorem fieldPicardSheafAlgebraicSpace : FieldPicardSheafAlgebraicSpaceStatement.{u} :=
  fieldPicardSheafAlgebraicSpace_of_stackAtlas fieldPicardStackAtlas

end Langlands.AlgebraicGeometry.Picard
