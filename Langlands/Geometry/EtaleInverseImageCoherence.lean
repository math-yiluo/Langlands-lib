import Langlands.Geometry.EtaleImageFunctoriality

/-! # Coherence of constructed small-etale inverse images -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open EtaleDirectImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem conjugate_leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {G G' : D ⥤ C}
    (a : L ⊣ G) (b : L' ⊣ G') (e : G ≅ G') :
    conjugateEquiv b a ((a.ofNatIsoRight e).leftAdjointUniq b).hom = e.inv := by
  ext Y
  apply ((a.homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  exact Adjunction.leftAdjointUniq_hom_app_counit (a.ofNatIsoRight e) b Y

variable {X Z V W : Scheme.{u}} (R : Type u) [CommRing R]

/-- The identity inverse-image comparison is conjugate to the inverse of
the actual geometric direct-image comparison. -/
theorem conjugate_inverseImageId (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id (inverseImageAdjunction (𝟙 X) R)
        (inverseImageId R X).hom =
      (directImageId (ModuleCat.{u} R) X).inv :=
  conjugate_leftAdjointUniq_ofNatIsoRight _ _ _

/-- Equality transport of inverse images is conjugate to the inverse of
the actual geometric direct-image equality comparison. -/
theorem conjugate_inverseImageCongr {f k : Z ⟶ X} (e : f = k) :
    conjugateEquiv (inverseImageAdjunction k R) (inverseImageAdjunction f R)
        (inverseImageCongr R e).hom =
      (directImageCongr (ModuleCat.{u} R) e).inv :=
  conjugate_leftAdjointUniq_ofNatIsoRight _ _ _

/-- The inverse-image composition comparison is conjugate to the inverse
of actual geometric direct-image composition. -/
theorem conjugate_inverseImageComp (f : Z ⟶ X) (g : V ⟶ Z) :
    conjugateEquiv (inverseImageAdjunction (g ≫ f) R)
        ((inverseImageAdjunction f R).comp (inverseImageAdjunction g R))
        (inverseImageComp R f g).hom =
      (directImageComp (ModuleCat.{u} R) f g).inv :=
  conjugate_leftAdjointUniq_ofNatIsoRight _ _ _

/-- Removing the identity at the target base agrees with the constructed
identity comparison, including transport of the composite base map. -/
theorem inverseImageComp_id_target (f : Z ⟶ X) :
    (inverseImageComp R (𝟙 X) f).hom ≫
        (inverseImageCongr R (Category.comp_id f)).hom =
      whiskerRight (inverseImageId R X).hom (inverseImage f R) ≫
        (inverseImage f R).leftUnitor.hom := by
  apply (conjugateEquiv (inverseImageAdjunction f R)
    ((inverseImageAdjunction (𝟙 X) R).comp (inverseImageAdjunction f R))).injective
  rw [← conjugateEquiv_comp _ (inverseImageAdjunction (f ≫ 𝟙 X) R),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (inverseImageAdjunction f R))]
  rw [conjugate_inverseImageCongr, conjugate_inverseImageComp,
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
    conjugate_inverseImageId]
  apply NatTrans.ext
  funext F
  change (directImageCongr (ModuleCat.{u} R) (Category.comp_id f)).inv.app F ≫
      (directImageComp (ModuleCat.{u} R) (𝟙 X) f).inv.app F =
    𝟙 _ ≫ (directImageId (ModuleCat.{u} R) X).inv.app
      ((directImage f (ModuleCat.{u} R)).obj F)
  rw [← directImageComp_id_target]
  simp

/-- Removing the identity at the source base agrees with the constructed
identity comparison, including transport of the composite base map. -/
theorem inverseImageComp_id_source (f : Z ⟶ X) :
    (inverseImageComp R f (𝟙 Z)).hom ≫
        (inverseImageCongr R (Category.id_comp f)).hom =
      whiskerLeft (inverseImage f R) (inverseImageId R Z).hom ≫
        (inverseImage f R).rightUnitor.hom := by
  apply (conjugateEquiv (inverseImageAdjunction f R)
    ((inverseImageAdjunction f R).comp (inverseImageAdjunction (𝟙 Z) R))).injective
  rw [← conjugateEquiv_comp _ (inverseImageAdjunction (𝟙 Z ≫ f) R),
    ← conjugateEquiv_comp _ ((inverseImageAdjunction f R).comp Adjunction.id)]
  rw [conjugate_inverseImageCongr, conjugate_inverseImageComp,
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
    conjugate_inverseImageId]
  apply NatTrans.ext
  funext F
  change (directImageCongr (ModuleCat.{u} R) (Category.id_comp f)).inv.app F ≫
      (directImageComp (ModuleCat.{u} R) f (𝟙 Z)).inv.app F =
    𝟙 _ ≫ (directImage f (ModuleCat.{u} R)).map
      ((directImageId (ModuleCat.{u} R) Z).inv.app F)
  rw [← directImageComp_id_source]
  simp

/-- The two triple inverse-image comparisons agree, including functor
associativity and transport of the associativity equality of base maps. -/
theorem inverseImageComp_assoc (f : Z ⟶ X) (g : V ⟶ Z) (h : W ⟶ V) :
    whiskerRight (inverseImageComp R f g).hom (inverseImage h R) ≫
        (inverseImageComp R (g ≫ f) h).hom =
      ((associator (inverseImage f R) (inverseImage g R) (inverseImage h R)).hom ≫
          whiskerLeft (inverseImage f R) (inverseImageComp R g h).hom ≫
          (inverseImageComp R f (h ≫ g)).hom) ≫
        (inverseImageCongr R (Category.assoc h g f)).hom := by
  apply (conjugateEquiv (inverseImageAdjunction (h ≫ g ≫ f) R)
    (((inverseImageAdjunction f R).comp (inverseImageAdjunction g R)).comp
      (inverseImageAdjunction h R))).injective
  rw [← conjugateEquiv_comp _
      ((inverseImageAdjunction (g ≫ f) R).comp (inverseImageAdjunction h R)),
    ← conjugateEquiv_comp _ (inverseImageAdjunction ((h ≫ g) ≫ f) R),
    ← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp
        ((inverseImageAdjunction g R).comp (inverseImageAdjunction h R))),
    ← conjugateEquiv_comp _
      ((inverseImageAdjunction f R).comp (inverseImageAdjunction (h ≫ g) R))]
  simp only [conjugate_inverseImageComp, conjugate_inverseImageCongr,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom]
  apply NatTrans.ext
  funext F
  change (directImageComp (ModuleCat.{u} R) (g ≫ f) h).inv.app F ≫
      (directImageComp (ModuleCat.{u} R) f g).inv.app
        ((directImage h (ModuleCat.{u} R)).obj F) =
    (directImageCongr (ModuleCat.{u} R) (Category.assoc h g f)).inv.app F ≫
      ((directImageComp (ModuleCat.{u} R) f (h ≫ g)).inv.app F ≫
        ((directImage f (ModuleCat.{u} R)).map
          ((directImageComp (ModuleCat.{u} R) g h).inv.app F) ≫ 𝟙 _))
  have he :
      (directImage f (ModuleCat.{u} R)).mapIso
          ((directImageComp (ModuleCat.{u} R) g h).app F) ≪≫
        (directImageComp (ModuleCat.{u} R) f (h ≫ g)).app F =
      (directImageComp (ModuleCat.{u} R) f g).app
          ((directImage h (ModuleCat.{u} R)).obj F) ≪≫
        (directImageComp (ModuleCat.{u} R) (g ≫ f) h).app F ≪≫
        ((directImageCongr (ModuleCat.{u} R) (Category.assoc h g f)).app F).symm := by
    apply Iso.ext
    exact directImageComp_assoc (ModuleCat.{u} R) f g h F
  have hi := congrArg Iso.inv he
  change (directImageComp (ModuleCat.{u} R) f (h ≫ g)).inv.app F ≫
      (directImage f (ModuleCat.{u} R)).map
        ((directImageComp (ModuleCat.{u} R) g h).inv.app F) =
    ((directImageCongr (ModuleCat.{u} R) (Category.assoc h g f)).hom.app F ≫
      (directImageComp (ModuleCat.{u} R) (g ≫ f) h).inv.app F) ≫
      (directImageComp (ModuleCat.{u} R) f g).inv.app
        ((directImage h (ModuleCat.{u} R)).obj F) at hi
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Category.id_comp,
    Category.comp_id] using
    (congrArg (fun a =>
      (directImageCongr (ModuleCat.{u} R) (Category.assoc h g f)).inv.app F ≫ a) hi).symm

/-- The triple inverse-image comparison, with its alternative construction
proved equal below. -/
def inverseImageTripleComp (f : Z ⟶ X) (g : V ⟶ Z) (h : W ⟶ V) :
    (inverseImage f R ⋙ inverseImage g R) ⋙ inverseImage h R ≅
      inverseImage (h ≫ g ≫ f) R :=
  isoWhiskerRight (inverseImageComp R f g) (inverseImage h R) ≪≫
    inverseImageComp R (g ≫ f) h

/-- The constructed triple comparison is independent of which adjacent
pair is combined first, with all associativity comparisons retained. -/
theorem inverseImageTripleComp_eq (f : Z ⟶ X) (g : V ⟶ Z) (h : W ⟶ V) :
    inverseImageTripleComp R f g h =
      associator (inverseImage f R) (inverseImage g R) (inverseImage h R) ≪≫
        isoWhiskerLeft (inverseImage f R) (inverseImageComp R g h) ≪≫
        inverseImageComp R f (h ≫ g) ≪≫
        inverseImageCongr R (Category.assoc h g f) := by
  apply Iso.ext
  simpa only [inverseImageTripleComp, Iso.trans_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, Category.assoc] using inverseImageComp_assoc R f g h

end Langlands.Geometry.EtaleInverseImage
