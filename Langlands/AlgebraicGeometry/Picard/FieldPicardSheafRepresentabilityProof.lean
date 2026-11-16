import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityReduction
import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasProof

/-! # Scheme representability of the fppf Picard sheaf over a field: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual fppf Picard sheaf of a proper scheme over any field is represented
by a separated scheme locally of finite type over that field. The published
reduction to the Picard stack atlas is applied to the published proof of that
atlas. -/
theorem fieldPicardSheafRepresentability :
    FieldPicardSheafRepresentabilityStatement.{u} :=
  fieldPicardSheafRepresentability_of_stackAtlas fieldPicardStackAtlas

end Langlands.AlgebraicGeometry.Picard
