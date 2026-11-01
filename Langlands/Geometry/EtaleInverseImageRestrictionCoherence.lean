import Langlands.Geometry.EtaleInverseImageRestriction
import Langlands.Geometry.EtaleInverseImageCoherence
import Langlands.Geometry.EtaleCohomologyDiagram

/-! # Coherence of the geometric inverse-image/restriction comparison -/

noncomputable section

universe u uA vA

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleDirectImage Langlands.Shimura.Coefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (A : Type uA) [Category.{vA} A]

@[simp] theorem restriction_map_hom_app
    (f : Z ⟶ X) [Etale f] {F G : Sheaf X.smallEtaleTopology A}
    (φ : F ⟶ G) (U : Z.Etaleᵒᵖ) :
    ((EtalePullback.restriction f A).map φ).hom.app U =
      φ.hom.app (op ((EtalePullback.siteMap f).obj U.unop)) := rfl

@[simp] theorem restrictionId_hom_app_hom_app (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((EtalePullback.restrictionId A).hom.app F).hom.app U =
      F.obj.map ((MorphismProperty.Over.mapId (P := @Etale) ⊤ X).inv.app U.unop).op := by
  dsimp [EtalePullback.restrictionId]
  simp only [Category.comp_id]

@[simp] theorem restrictionComp_hom_app_hom_app
    (f : Z ⟶ X) [Etale f] (g : V ⟶ Z) [Etale g]
    (F : Sheaf X.smallEtaleTopology A) (U : V.Etaleᵒᵖ) :
    ((EtalePullback.restrictionComp f A g).hom.app F).hom.app U =
      F.obj.map ((MorphismProperty.Over.mapComp ⊤
        (inferInstance : Etale g) (inferInstance : Etale f)).hom.app U.unop).op := rfl

@[simp] theorem restrictionGeometricAdjunction_counit_app_hom_app
    (f : Z ⟶ X) [Etale f] (F : Sheaf Z.smallEtaleTopology A) (U : Z.Etaleᵒᵖ) :
    ((restrictionGeometricAdjunction f A).counit.app F).hom.app U =
      F.obj.map ((EtalePullback.siteMapPullbackAdjunction f).unit.app U.unop).op := by
  simp [restrictionGeometricAdjunction]

@[simp] theorem directImageComp_inv_app_hom_app
    (f : Z ⟶ X) (g : V ⟶ Z) (F : Sheaf V.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((directImageComp A f g).inv.app F).hom.app U =
      F.obj.map ((etaleObjectPullbackComp f g).inv.app U.unop).op := by
  simp [directImageComp]

/-- Identity restriction is conjugate to actual geometric direct-image identity. -/
theorem conjugate_restrictionId (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id
        (restrictionGeometricAdjunction (𝟙 X) A)
        (EtalePullback.restrictionId A).hom =
      (directImageId A X).inv := by
  apply NatTrans.ext
  funext F
  apply (((restrictionGeometricAdjunction (𝟙 X) A).homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    restrictionGeometricAdjunction_counit_app_hom_app,
    restriction_map_hom_app, directImageId_inv_app_hom_app,
    restrictionId_hom_app_hom_app, Adjunction.id_counit]
  change F.obj.map _ ≫ 𝟙 _ = F.obj.map _ ≫ F.obj.map _
  simp only [Category.comp_id, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [EtalePullback.siteMapPullbackAdjunction, etaleObjectPullbackId]

/-- Successive etale restrictions are conjugate to geometric direct-image
composition. -/
theorem conjugate_restrictionComp (f : Z ⟶ X) [Etale f] (g : V ⟶ Z) [Etale g] :
    conjugateEquiv (restrictionGeometricAdjunction (g ≫ f) A)
        ((restrictionGeometricAdjunction f A).comp
          (restrictionGeometricAdjunction g A))
        (EtalePullback.restrictionComp f A g).hom =
      (directImageComp A f g).inv := by
  apply NatTrans.ext
  funext F
  apply ((((restrictionGeometricAdjunction f A).comp
    (restrictionGeometricAdjunction g A)).homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_counit_app,
    restrictionGeometricAdjunction_counit_app_hom_app,
    Functor.comp_map, restriction_map_hom_app,
    directImageComp_inv_app_hom_app, restrictionComp_hom_app_hom_app]
  change F.obj.map _ ≫ F.obj.map _ =
    F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _
  simp only [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change
    ((EtalePullback.siteMapPullbackAdjunction (g ≫ f)).unit.app U.unop).left ≫
        ((etaleObjectPullback (g ≫ f)).map
          ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
            (inferInstance : Etale f)).hom.app U.unop)).left =
      ((EtalePullback.siteMapPullbackAdjunction g).unit.app U.unop).left ≫
        ((etaleObjectPullback g).map
          ((EtalePullback.siteMapPullbackAdjunction f).unit.app
            ((EtalePullback.siteMap g).obj U.unop))).left ≫
        ((etaleObjectPullbackComp f g).inv.app _).left
  apply pullback.hom_ext <;>
    simp [EtalePullback.siteMapPullbackAdjunction, etaleObjectPullbackComp,
      MorphismProperty.Over.pullbackComp, etaleObjectPullback]

variable (R : Type u) [CommRing R]

/-- The canonical comparison has the identity on geometric direct image as mate. -/
theorem conjugate_inverseImageIsoRestriction (f : Z ⟶ X) [Etale f] :
    conjugateEquiv (restrictionGeometricAdjunction f (ModuleCat.{u} R))
        (inverseImageAdjunction f R) (inverseImageIsoRestriction f R).hom =
      𝟙 _ := by
  apply NatTrans.ext
  funext F
  apply (((inverseImageAdjunction f R).homEquiv _ _).symm).injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Adjunction.leftAdjointUniq_hom_app_counit (inverseImageAdjunction f R)
    (restrictionGeometricAdjunction f (ModuleCat.{u} R)) F

/-- The constructed comparison respects identity pullback. -/
theorem inverseImageIsoRestriction_id (X : Scheme.{u}) :
    (inverseImageIsoRestriction (𝟙 X) R).hom ≫
        (EtalePullback.restrictionId (ModuleCat.{u} R)).hom =
      (inverseImageId R X).hom := by
  apply (conjugateEquiv Adjunction.id (inverseImageAdjunction (𝟙 X) R)).injective
  rw [← conjugateEquiv_comp _
    (restrictionGeometricAdjunction (𝟙 X) (ModuleCat.{u} R)),
    conjugate_restrictionId, conjugate_inverseImageIsoRestriction,
    conjugate_inverseImageId, Category.comp_id]

/-- The constructed comparison respects composition of etale base morphisms. -/
theorem inverseImageIsoRestriction_comp (f : Z ⟶ X) [Etale f]
    (g : V ⟶ Z) [Etale g] :
    (inverseImageComp R f g).hom ≫ (inverseImageIsoRestriction (g ≫ f) R).hom =
      (Functor.whiskerRight (inverseImageIsoRestriction f R).hom (inverseImage g R) ≫
        Functor.whiskerLeft (EtalePullback.restriction f (ModuleCat.{u} R))
          (inverseImageIsoRestriction g R).hom) ≫
        (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom := by
  apply (conjugateEquiv (restrictionGeometricAdjunction (g ≫ f) (ModuleCat.{u} R))
    ((inverseImageAdjunction f R).comp (inverseImageAdjunction g R))).injective
  rw [← conjugateEquiv_comp _ (inverseImageAdjunction (g ≫ f) R),
    ← conjugateEquiv_comp _ ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).comp
      (restrictionGeometricAdjunction g (ModuleCat.{u} R))),
    ← conjugateEquiv_comp _ ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).comp
      (inverseImageAdjunction g R))]
  simp only [conjugate_inverseImageIsoRestriction, conjugate_inverseImageComp,
    conjugate_restrictionComp, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight, Category.id_comp]
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.id_app, CategoryTheory.Functor.map_id]
  change (directImageComp (ModuleCat.{u} R) f g).inv.app F =
    (directImageComp (ModuleCat.{u} R) f g).inv.app F ≫ 𝟙 _ ≫ 𝟙 _
  simp

/-- Compare successive geometric inverse images with restriction along the
composite by comparing the two individual inverse images first. -/
def compositeInverseImageIsoRestriction (f : Z ⟶ X) [Etale f]
    (g : V ⟶ Z) [Etale g] :
    inverseImage f R ⋙ inverseImage g R ≅
      EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R) :=
  isoWhiskerRight (inverseImageIsoRestriction f R) (inverseImage g R) ≪≫
    isoWhiskerLeft (EtalePullback.restriction f (ModuleCat.{u} R))
      (inverseImageIsoRestriction g R) ≪≫
    EtalePullback.restrictionComp f (ModuleCat.{u} R) g

/-- The successive comparison is the canonical comparison after geometric
composition. -/
theorem compositeInverseImageIsoRestriction_eq (f : Z ⟶ X) [Etale f]
    (g : V ⟶ Z) [Etale g] :
    compositeInverseImageIsoRestriction R f g =
      inverseImageComp R f g ≪≫ inverseImageIsoRestriction (g ≫ f) R := by
  apply Iso.ext
  simpa only [compositeInverseImageIsoRestriction, Iso.trans_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Category.assoc] using
    (inverseImageIsoRestriction_comp R f g).symm

/-- Restriction equality transport is conjugate to geometric direct-image
transport of the same equality. -/
theorem conjugate_restrictionCongr {f k : Z ⟶ X} [Etale f] [Etale k] (e : f = k) :
    conjugateEquiv (restrictionGeometricAdjunction k (ModuleCat.{u} R))
        (restrictionGeometricAdjunction f (ModuleCat.{u} R))
        (EtalePullback.restrictionCongr R e).hom =
      (directImageCongr (ModuleCat.{u} R) e).inv := by
  subst k
  simp only [EtalePullback.restrictionCongr, Iso.refl_hom, conjugateEquiv_id]
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have he : (etaleObjectPullbackCongr (rfl : f = f)).hom.app U.unop = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change _ = 𝟙 (pullback U.unop.hom f)
    apply pullback.hom_ext <;> simp
  change 𝟙 _ = F.obj.map ((etaleObjectPullbackCongr (rfl : f = f)).hom.app U.unop).op
  rw [he]
  exact (F.obj.map_id _).symm

/-- The constructed comparison respects equality transport of the base map. -/
theorem inverseImageIsoRestriction_congr {f k : Z ⟶ X} [Etale f] [Etale k]
    (e : f = k) :
    (inverseImageCongr R e).hom ≫ (inverseImageIsoRestriction k R).hom =
      (inverseImageIsoRestriction f R).hom ≫ (EtalePullback.restrictionCongr R e).hom := by
  apply (conjugateEquiv (restrictionGeometricAdjunction k (ModuleCat.{u} R))
    (inverseImageAdjunction f R)).injective
  rw [← conjugateEquiv_comp _ (inverseImageAdjunction k R),
    ← conjugateEquiv_comp _ (restrictionGeometricAdjunction f (ModuleCat.{u} R)),
    conjugate_inverseImageIsoRestriction, conjugate_inverseImageCongr,
    conjugate_restrictionCongr, conjugate_inverseImageIsoRestriction,
    Category.id_comp, Category.comp_id]

end Langlands.Geometry.EtaleInverseImage
