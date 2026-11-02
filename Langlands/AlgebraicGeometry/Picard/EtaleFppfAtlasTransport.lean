import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.Picard.EtaleFppfSheafComparison

/-! # Transport of actual Picard atlases from etale to fppf classes -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The full canonical etale-to-fppf Picard comparison, as an isomorphism of
ordinary presheaves, under the explicit fppf descent hypothesis. -/
def etaleFppfClassPresheafIso
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f)) :
    etaleClassSheafPresheaf f ≅ classSheafPresheaf f :=
  (sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).mapIso
    (etaleFppfClassSheafIso f hF)

@[simp]
lemma etaleFppfClassPresheafIso_hom
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f)) :
    (etaleFppfClassPresheafIso f hF).hom = (etaleToFppfClassSheaf f).hom := rfl

@[reassoc (attr := simp)]
lemma toEtaleClassSheaf_etaleFppfClassPresheafIso_hom
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f)) :
    toEtaleClassSheaf f ≫ (etaleFppfClassPresheafIso f hF).hom = toClassSheaf f :=
  toEtaleClassSheaf_etaleToFppf f

/-- A full etale-class diagonal and locally finite type etale-surjective
scheme atlas give those same geometric conditions for the actual fppf
Picard sheaf, provided the etale class sheaf satisfies fppf descent. -/
theorem classSheaf_algebraicSpace_of_etale_atlas
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f))
    (hD : AlgebraicSpace.HasRepresentableDiagonal (etaleClassSheafPresheaf f))
    (hA : ∃ (U : Over S)
      (a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ etaleClassSheafPresheaf f),
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
        LocallyOfFiniteType U.hom) :
    AlgebraicSpace.IsAlgebraicSpace S (classSheaf f) ∧
      ∃ (U : Over S)
        (a : (AlgebraicSpace.schemeYoneda S).obj U ⟶ classSheafPresheaf f),
        AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
          LocallyOfFiniteType U.hom := by
  have hD' := AlgebraicSpace.hasRepresentableDiagonal_of_iso
    (etaleFppfClassPresheafIso f hF) hD
  obtain ⟨U, a, ha, hs, hU⟩ :=
    AlgebraicSpace.exists_locallyFiniteType_atlas_of_iso
      (etaleFppfClassPresheafIso f hF) hA
  exact ⟨⟨hD', U, a, ha, hs⟩, U, a, ha, hs, hU⟩

end Langlands.AlgebraicGeometry.Picard.RelativePicard
