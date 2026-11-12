import Langlands.AlgebraicGeometry.Picard.FieldPicardClosedDiagonal
import Langlands.AlgebraicGeometry.Picard.TrivialLocusNoetherian
import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphismEtaleAtlasProof
import Langlands.AlgebraicGeometry.Picard.CoherentAtlasTransfer
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAtlasFppfSheafProof

/-! # The proper-field Picard algebraic space from a Picard stack atlas -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A field Picard stack atlas makes the actual etale Picard class sheaf an fppf
sheaf: the stack atlas gives it a representable diagonal and an etale scheme
atlas, and such an etale sheaf satisfies fppf descent. -/
theorem fieldEtaleFppfClassSheaf_of_stackAtlas
    (hA : FieldPicardStackAtlasStatement.{u}) :
    FieldEtaleFppfClassSheafStatement.{u} := by
  intro k _ X hX
  obtain ⟨hD, U, a, ha, hs, -⟩ :=
    fieldEtalePicardAtlas_of_stackInputs hA smoothAutomorphismEtaleAtlas k X hX
  exact AlgebraicSpace.etaleAtlasFppfSheaf _ _
    (RelativePicard.etaleClassSheaf X.hom).property hD ⟨U, a, ha, hs⟩

/-- The exact proper-field Picard algebraic-space proposition follows from the
field Picard stack atlas alone. -/
theorem fieldPicardSheafAlgebraicSpace_of_stackAtlas
    (hA : FieldPicardStackAtlasStatement.{u}) :
    FieldPicardSheafAlgebraicSpaceStatement.{u} :=
  fieldPicardSheafAlgebraicSpace_of_stackInputs
    RelativePicard.fieldPicardClassEqualizerImmersion hA smoothAutomorphismEtaleAtlas
    (fieldEtaleFppfClassSheaf_of_stackAtlas hA)

/-- The same conclusion from a coherent-family stack atlas over every field. -/
theorem fieldPicardSheafAlgebraicSpace_of_coherentStackAtlas
    (h : CoherentSheaves.FieldCoherentStackAtlasStatement.{u}) :
    FieldPicardSheafAlgebraicSpaceStatement.{u} :=
  fieldPicardSheafAlgebraicSpace_of_stackAtlas
    (fieldPicardStackAtlas_of_coherentStackAtlas h)

set_option linter.defProp false in
/-- The implication proved by `fieldPicardSheafAlgebraicSpace_of_stackAtlas`, as a
single term from the field Picard stack atlas to the exact target. -/
def fieldPicardSheafAlgebraicSpaceOfStackAtlas :
    FieldPicardStackAtlasStatement.{u} → FieldPicardSheafAlgebraicSpaceStatement.{u} :=
  fieldPicardSheafAlgebraicSpace_of_stackAtlas

end Langlands.AlgebraicGeometry.Picard
