import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedAddCommGroupSheafSchemeRepresentabilityProof

/-! # Reduction of the proper-field Picard scheme to the Picard stack atlas -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- Scheme representability of the actual fppf Picard sheaf from its separated
algebraic-space structure. -/
theorem fieldPicardSheafRepresentability_of_algebraicSpace
    (h : FieldPicardSheafAlgebraicSpaceStatement.{u}) :
    FieldPicardSheafRepresentabilityStatement.{u} := by
  intro k _ X hX
  obtain ⟨hAlg, hClosed, hAtlas⟩ := h k X hX
  exact AlgebraicSpace.separatedAddCommGroupSheafSchemeRepresentability k
    (RelativePicard.classSheaf X.hom) (RelativePicard.sheafPresheaf X.hom)
    ⟨RelativePicard.forgetSheafIso X.hom⟩ hAlg hClosed hAtlas

/-- Scheme representability of the actual fppf Picard sheaf, with the Picard
stack atlas as the only remaining input. -/
theorem fieldPicardSheafRepresentability_of_stackAtlas
    (hA : FieldPicardStackAtlasStatement.{u}) :
    FieldPicardSheafRepresentabilityStatement.{u} :=
  fieldPicardSheafRepresentability_of_algebraicSpace
    (fieldPicardSheafAlgebraicSpace_of_stackAtlas hA)

/-- A chosen actual scheme over the field with a chosen natural representation
of the full fppf Picard sheaf, retaining the Picard stack atlas as an explicit
input. -/
def fieldPicardScheme (hA : FieldPicardStackAtlasStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    Σ (P : Over (Spec (CommRingCat.of k))),
      (RelativePicard.classSheafPresheaf X.hom).RepresentableBy P :=
  let h := fieldPicardSheafRepresentability_of_stackAtlas hA k X hX
  ⟨h.choose, h.choose_spec.2.2.some⟩

/-- The chosen representing scheme is separated over the field. -/
lemma fieldPicardScheme_isSeparated (hA : FieldPicardStackAtlasStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    IsSeparated (fieldPicardScheme hA k X hX).1.hom :=
  (fieldPicardSheafRepresentability_of_stackAtlas hA k X hX).choose_spec.1

/-- The chosen representing scheme is locally of finite type over the field. -/
lemma fieldPicardScheme_locallyOfFiniteType
    (hA : FieldPicardStackAtlasStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    LocallyOfFiniteType (fieldPicardScheme hA k X hX).1.hom :=
  (fieldPicardSheafRepresentability_of_stackAtlas hA k X hX).choose_spec.2.1

end Langlands.AlgebraicGeometry.Picard
