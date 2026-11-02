import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Langlands.AlgebraicGeometry.Sites.EtaleFppfComparison
import Langlands.CategoryTheory.Sites.SheafificationComparison

/-! # Comparing the etale and fppf sheaves of ordinary Picard classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The etale sheafification of ordinary relative line-bundle classes. -/
def etaleClassSheaf : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.etaleTopology.over S) (Type (u + 1))).obj (classPresheaf f)

/-- The underlying presheaf of the etale class sheaf. -/
def etaleClassSheafPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (etaleClassSheaf f).obj

/-- The etale sheafification unit on ordinary relative classes. -/
def toEtaleClassSheaf : classPresheaf f ⟶ etaleClassSheafPresheaf f :=
  toSheafify (Scheme.etaleTopology.over S) (classPresheaf f)

/-- The canonical map from etale to fppf sheafification, on the full slice site. -/
def etaleToFppfClassSheaf :
    etaleClassSheaf f ⟶ (Sites.fppfSheafToEtaleSheaf S (Type (u + 1))).obj
      (classSheaf f) :=
  ⟨Langlands.CategoryTheory.SheafificationComparison.comparison
    (Scheme.etaleTopology.over S) (Scheme.fppfTopology.over S)
    (Sites.etaleTopologyOver_le_fppfTopologyOver S) (classPresheaf f)⟩

@[reassoc (attr := simp)]
lemma toEtaleClassSheaf_etaleToFppf :
    toEtaleClassSheaf f ≫ (etaleToFppfClassSheaf f).hom = toClassSheaf f :=
  Langlands.CategoryTheory.SheafificationComparison.toSheafify_comparison _ _
    (Sites.etaleTopologyOver_le_fppfTopologyOver S) _

/-- An actual bundle has the same class under the canonical comparison. -/
lemma etaleToFppfClassSheaf_classOf (T : Over S)
    (L : LineBundle ((relativeSpace f).obj T)) :
    (etaleToFppfClassSheaf f).hom.app (op T)
        ((toEtaleClassSheaf f).app (op T) (classOf f T L)) =
      sheafClassOf f T L :=
  congrArg (fun η ↦ η.app (op T) (classOf f T L))
    (toEtaleClassSheaf_etaleToFppf f)

/-- The comparison is invertible if the etale class sheaf satisfies fppf descent. -/
def etaleFppfClassSheafIso
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f)) :
    etaleClassSheaf f ≅ (Sites.fppfSheafToEtaleSheaf S (Type (u + 1))).obj
      (classSheaf f) :=
  ObjectProperty.isoMk _
    (Langlands.CategoryTheory.SheafificationComparison.comparisonIso
      (Scheme.etaleTopology.over S) (Scheme.fppfTopology.over S)
      (Sites.etaleTopologyOver_le_fppfTopologyOver S) (classPresheaf f) hF)

@[simp]
lemma etaleFppfClassSheafIso_hom
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f)) :
    (etaleFppfClassSheafIso f hF).hom = etaleToFppfClassSheaf f := rfl

@[reassoc (attr := simp)]
lemma toClassSheaf_etaleFppfClassSheafIso_inv
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (etaleClassSheafPresheaf f)) :
    toClassSheaf f ≫ (etaleFppfClassSheafIso f hF).inv.hom = toEtaleClassSheaf f :=
  Langlands.CategoryTheory.SheafificationComparison.toSheafify_comparisonIso_inv _ _
    (Sites.etaleTopologyOver_le_fppfTopologyOver S) _ hF

end Langlands.AlgebraicGeometry.Picard.RelativePicard
