import Langlands.AlgebraicGeometry.Picard.SmoothDoubleQuotient
import Langlands.AlgebraicGeometry.Picard.SmoothAtlasLocalSurjectivity
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Reduction of the Picard atlas theorem to the generic smooth quotient -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open PicardGroupoid

/-- The published descent and local-surjectivity results discharge those
inputs of the double quotient, leaving only the generic quotient theorem. -/
lemma smoothAutomorphism_picardProperties_of_smoothRelationQuotient
    (hQuot : AlgebraicSpace.SmoothRelationQuotientStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hAtlas : HasLocallyFiniteTypeSmoothSchemeAtlas f)
    (hAut : HasSmoothRelativeAutomorphismSchemes f) :
    Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S)
      (RelativePicard.etaleClassSheafPresheaf f) ∧
    AlgebraicSpace.HasRepresentableDiagonal
      (RelativePicard.etaleClassSheafPresheaf f) ∧
    ∃ (V : Over S)
      (a : (AlgebraicSpace.schemeYoneda S).obj V ⟶
        RelativePicard.etaleClassSheafPresheaf f),
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
        LocallyOfFiniteType V.hom := by
  obtain ⟨U, L, hU, hL⟩ := hAtlas
  have hDescent : ∀ (P W V : Scheme.{u}) (p : P ⟶ W) (g : W ⟶ V),
      Smooth p → Surjective p → Smooth (p ≫ g) → Smooth g := by
    intro P W V p g hp hs hpg
    exact @smooth_of_smooth_of_surjective_of_smooth_comp P W V p g hp hs hpg
  exact smoothDoubleQuotient_picardProperties hQuot hDescent f L hL hU hAut
    (etaleFamilyMap_isLocallySurjective f L hL)

/-- The actual ordinary Picard presheaf as an algebraic space, conditional
only on the generic smooth-relation quotient theorem. -/
def smoothAutomorphismQuotientPicardSpace
    (hQuot : AlgebraicSpace.SmoothRelationQuotientStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hAtlas : HasLocallyFiniteTypeSmoothSchemeAtlas f)
    (hAut : HasSmoothRelativeAutomorphismSchemes f) : AlgebraicSpace S :=
  let h := smoothAutomorphism_picardProperties_of_smoothRelationQuotient
    hQuot f hAtlas hAut
  ⟨⟨RelativePicard.etaleClassSheafPresheaf f, h.1⟩, h.2.1, by
    obtain ⟨V, a, ha, hs, _hV⟩ := h.2.2
    exact ⟨V, a, ha, hs⟩⟩

/-- This conditional space has literally the original ordinary presheaf. -/
lemma smoothAutomorphismQuotientPicardSpace_presheaf
    (hQuot : AlgebraicSpace.SmoothRelationQuotientStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hAtlas : HasLocallyFiniteTypeSmoothSchemeAtlas f)
    (hAut : HasSmoothRelativeAutomorphismSchemes f) :
    (smoothAutomorphismQuotientPicardSpace hQuot f hAtlas hAut).presheaf =
      RelativePicard.etaleClassSheafPresheaf f := rfl

/-- The exact Picard target follows from the generic smooth quotient
proposition, which remains an explicit hypothesis of this reduction. -/
theorem smoothAutomorphismEtaleAtlas_of_smoothRelationQuotient
    (hQuot : AlgebraicSpace.SmoothRelationQuotientStatement.{u}) :
    SmoothAutomorphismEtaleAtlasStatement.{u} := by
  intro S X f _hStack hAtlas hAut
  exact
    (smoothAutomorphism_picardProperties_of_smoothRelationQuotient
      hQuot f hAtlas hAut).2

end Langlands.AlgebraicGeometry.Picard
