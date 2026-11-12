import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement
import Langlands.AlgebraicGeometry.Picard.StackAtlasBaseChange
import Langlands.AlgebraicGeometry.Picard.ProperFlatFiniteTypeModel

/-! # Reduction of the field Picard stack atlas to finite-type `ℤ`-algebras -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Smooth scheme atlases of the actual Picard stack over finite-type `ℤ`-algebras give
smooth scheme atlases over every field: spread the proper scheme out to a proper flat
model over a finite-type `ℤ`-algebra and base change that model's atlas. -/
theorem fieldPicardStackAtlas_of_finiteType
    (h : FiniteTypePicardStackAtlasStatement.{u}) :
    FieldPicardStackAtlasStatement.{u} := by
  intro k _ X hX
  obtain ⟨R, _, _, _, X₀, p₀, π, hp, hf, hpb⟩ := field_hasProperFlatFiniteTypeModel k X hX
  exact PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_of_isPullback hpb
    (h R (Over.mk p₀) hp hf)

set_option linter.defProp false in
/-- The implication proved by `fieldPicardStackAtlas_of_finiteType`, as a single term
from the finite-type Picard stack atlas statement to the field statement. -/
def fieldPicardStackAtlasOfFiniteType :
    FiniteTypePicardStackAtlasStatement.{u} → FieldPicardStackAtlasStatement.{u} :=
  fieldPicardStackAtlas_of_finiteType

end Langlands.AlgebraicGeometry.Picard
