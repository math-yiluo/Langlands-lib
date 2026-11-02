import Langlands.AlgebraicGeometry.Picard.ArrowQuotientClassKernel
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport

/-! # Recognition of the second Picard arrow-class quotient -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open AlgebraicSpace.SmoothRelationQuotient

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  {A R : Over S} (r s : R ⟶ A)
  (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
  (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
    ((AlgebraicSpace.schemeYoneda S).map s)
    (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L))
  (hF : CategoryTheory.Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S)
    (arrowKernelQuotientSheaf f L r s eA h).obj)
  (hD : AlgebraicSpace.HasRepresentableDiagonal
    (arrowKernelQuotientSheaf f L r s eA h).obj)
  (hAtlas : ∃ (W : Over S)
    (b : (AlgebraicSpace.schemeYoneda S).obj W ⟶
      (arrowKernelQuotientSheaf f L r s eA h).obj),
    AlgebraicSpace.IsEtale b ∧ AlgebraicSpace.IsSurjective b)

/-- The first canonical arrow-class quotient, packaged as an algebraic space
under its explicit geometric hypotheses. -/
def arrowKernelQuotientSpace : AlgebraicSpace S :=
  ⟨⟨(arrowKernelQuotientSheaf f L r s eA h).obj, hF⟩, hD, hAtlas⟩

/-- The full arrow-class sheaf defines an equivalence relation on the object
scheme; no choice of global representatives is imposed. -/
lemma arrowKernelQuotientSpace_isEquivalenceRelation :
    IsEquivalenceRelation (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
      (arrowKernelQuotientFst f L r s eA h)
      (arrowKernelQuotientSnd f L r s eA h) :=
  arrowKernelQuotient_sectionwise f L r s eA h

/-- The second canonical etale quotient, now taking classes of objects under
the complete relation of arrow classes. -/
def arrowClassQuotientSheaf : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  quotientSheaf (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
    (arrowKernelQuotientFst f L r s eA h)
    (arrowKernelQuotientSnd f L r s eA h)
    (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA h hF hD hAtlas)

/-- The fixed quotient map from the original object scheme. -/
def arrowClassQuotientMap :
    (AlgebraicSpace.schemeYoneda S).obj U ⟶
      (arrowClassQuotientSheaf f L r s eA h hF hD hAtlas).obj :=
  quotientMap (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
    (arrowKernelQuotientFst f L r s eA h)
    (arrowKernelQuotientSnd f L r s eA h)
    (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA h hF hD hAtlas)

variable (hLocal : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
  (etaleFamilyMap f L))

/-- If the actual family map is etale locally surjective, the second canonical
quotient is the actual etale sheaf of Picard groupoid classes. -/
def arrowClassQuotientIso :
    (arrowClassQuotientSheaf f L r s eA h hF hD hAtlas).obj ≅
      (relativeEtaleClassSheaf f).obj :=
  quotientSheafIsoOfPresentation
    (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
    (arrowKernelQuotientFst f L r s eA h)
    (arrowKernelQuotientSnd f L r s eA h)
    (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA h hF hD hAtlas)
    (relativeEtaleClassSheaf f).property
    (𝟙 ((AlgebraicSpace.schemeYoneda S).obj U)) (etaleFamilyMap f L)
    (by
      simpa only [Category.id_comp] using
        isLocallySurjective_quotientMap
          (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
          (arrowKernelQuotientFst f L r s eA h)
          (arrowKernelQuotientSnd f L r s eA h)
          (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA h hF hD hAtlas))
    hLocal
    (fun T x y ↦ (arrowKernelQuotient_relation_iff f L r s eA h
      (T := T) ⟨x⟩ ⟨y⟩).symm)

/-- Recognition preserves the whole original family presentation. -/
@[reassoc]
lemma arrowClassQuotientIso_hom_fac :
    arrowClassQuotientMap f L r s eA h hF hD hAtlas ≫
      (arrowClassQuotientIso f L r s eA h hF hD hAtlas hLocal).hom =
        etaleFamilyMap f L := by
  apply (Category.id_comp _).symm.trans
  exact quotientSheafIsoOfPresentation_hom_fac
      (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
      (arrowKernelQuotientFst f L r s eA h)
      (arrowKernelQuotientSnd f L r s eA h)
      (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA h hF hD hAtlas)
      (relativeEtaleClassSheaf f).property
      (𝟙 ((AlgebraicSpace.schemeYoneda S).obj U)) (etaleFamilyMap f L)
      (by
        simpa only [Category.id_comp] using
          isLocallySurjective_quotientMap
            (arrowKernelQuotientSpace f L r s eA h hF hD hAtlas)
            (arrowKernelQuotientFst f L r s eA h)
            (arrowKernelQuotientSnd f L r s eA h)
            (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA h hF hD hAtlas))
      hLocal
      (fun T x y ↦ (arrowKernelQuotient_relation_iff f L r s eA h
        (T := T) ⟨x⟩ ⟨y⟩).symm)

/-- The second quotient agrees naturally with ordinary etale Picard classes. -/
def arrowClassQuotientPicardIso :
    (arrowClassQuotientSheaf f L r s eA h hF hD hAtlas).obj ≅
      RelativePicard.etaleClassSheafPresheaf f :=
  arrowClassQuotientIso f L r s eA h hF hD hAtlas hLocal ≪≫
    (sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).mapIso
      (relativeEtaleClassSheafIso f)

/-- The ordinary comparison preserves the actual line-bundle family class. -/
@[reassoc]
lemma arrowClassQuotientPicardIso_hom_fac :
    arrowClassQuotientMap f L r s eA h hF hD hAtlas ≫
      (arrowClassQuotientPicardIso f L r s eA h hF hD hAtlas hLocal).hom =
        uliftYonedaEquiv.symm
          ((RelativePicard.toEtaleClassSheaf f).app (op U)
            (RelativePicard.classOf f U L)) := by
  change arrowClassQuotientMap f L r s eA h hF hD hAtlas ≫
      (arrowClassQuotientIso f L r s eA h hF hD hAtlas hLocal).hom ≫
        (relativeEtaleClassSheafIso f).hom.hom = _
  rw [← Category.assoc, arrowClassQuotientIso_hom_fac, etaleFamilyMap_comparison]

include hLocal in
/-- Diagonal representability and a locally finite type etale atlas of the
second quotient transfer to the ordinary Picard class sheaf. -/
lemma arrowClassQuotient_picardAtlas
    (hD₂ : AlgebraicSpace.HasRepresentableDiagonal
      (arrowClassQuotientSheaf f L r s eA h hF hD hAtlas).obj)
    (hAtlas₂ : ∃ (V : Over S)
      (a : (AlgebraicSpace.schemeYoneda S).obj V ⟶
        (arrowClassQuotientSheaf f L r s eA h hF hD hAtlas).obj),
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
        LocallyOfFiniteType V.hom) :
    AlgebraicSpace.HasRepresentableDiagonal
      (RelativePicard.etaleClassSheafPresheaf f) ∧
    ∃ (V : Over S)
      (a : (AlgebraicSpace.schemeYoneda S).obj V ⟶
        RelativePicard.etaleClassSheafPresheaf f),
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
        LocallyOfFiniteType V.hom :=
  ⟨AlgebraicSpace.hasRepresentableDiagonal_of_iso
      (arrowClassQuotientPicardIso f L r s eA h hF hD hAtlas hLocal) hD₂,
    AlgebraicSpace.exists_locallyFiniteType_atlas_of_iso
      (arrowClassQuotientPicardIso f L r s eA h hF hD hAtlas hLocal) hAtlas₂⟩

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
