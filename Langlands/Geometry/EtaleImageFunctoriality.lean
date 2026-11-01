import Langlands.Geometry.EtaleInverseImage
import Langlands.Shimura.Coefficients.EtaleTorsorPullbackCoherence

/-! # Identity and composition of arbitrary-scheme etale sheaf images -/

noncomputable section

universe u uA vA

namespace Langlands.Geometry.EtaleDirectImage

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Shimura.Coefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V W : Scheme.{u}} (A : Type uA) [Category.{vA} A]

/-- Direct image along the identity is the identity, by the actual
fiber-product first projection. -/
def directImageId (X : Scheme.{u}) :
    directImage (𝟙 X) A ≅ 𝟭 (Sheaf X.smallEtaleTopology A) :=
  Functor.sheafPushforwardContinuousId' (etaleObjectPullbackId X) A X.smallEtaleTopology

/-- Equal base maps give the actual fiber-product comparison on direct images. -/
def directImageCongr {f k : Z ⟶ X} (e : f = k) :
    directImage f A ≅ directImage k A :=
  Functor.sheafPushforwardContinuousIso (etaleObjectPullbackCongr e)
    A X.smallEtaleTopology Z.smallEtaleTopology

/-- Successive direct images identify with direct image along the composite. -/
def directImageComp (f : Z ⟶ X) (g : V ⟶ Z) :
    directImage g A ⋙ directImage f A ≅ directImage (g ≫ f) A :=
  Functor.sheafPushforwardContinuousComp' (etaleObjectPullbackComp f g).symm
    A X.smallEtaleTopology Z.smallEtaleTopology V.smallEtaleTopology

@[simp] theorem directImageId_inv_app_hom_app (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((directImageId A X).inv.app F).hom.app U =
      F.obj.map ((etaleObjectPullbackId X).hom.app U.unop).op := by
  simp [directImageId]

@[simp] theorem directImageCongr_inv_app_hom_app {f k : Z ⟶ X} (e : f = k)
    (F : Sheaf Z.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((directImageCongr A e).inv.app F).hom.app U =
      F.obj.map ((etaleObjectPullbackCongr e).hom.app U.unop).op := rfl

@[simp] theorem directImageComp_hom_app_hom_app (f : Z ⟶ X) (g : V ⟶ Z)
    (F : Sheaf V.smallEtaleTopology A) (U : X.Etaleᵒᵖ) :
    ((directImageComp A f g).hom.app F).hom.app U =
      F.obj.map ((etaleObjectPullbackComp f g).hom.app U.unop).op := by
  simp [directImageComp]

/-- Target-base identity coherence on all sheaf morphisms. -/
theorem directImageComp_id_target (f : Z ⟶ X) (F : Sheaf Z.smallEtaleTopology A) :
    (directImageId A X).inv.app ((directImage f A).obj F) ≫
        (directImageComp A (𝟙 X) f).hom.app F =
      (directImageCongr A (Category.comp_id f)).inv.app F := by
  apply Sheaf.hom_ext
  ext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    directImageId_inv_app_hom_app,
    directImageComp_hom_app_hom_app, directImageCongr_inv_app_hom_app]
  change F.obj.map ((etaleObjectPullback f).map
      ((etaleObjectPullbackId X).hom.app U.unop)).op ≫
    F.obj.map ((etaleObjectPullbackComp (𝟙 X) f).hom.app U.unop).op =
    F.obj.map ((etaleObjectPullbackCongr (Category.comp_id f)).hom.app U.unop).op
  rw [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact etaleObjectPullbackComp_id_target f U.unop

/-- Source-base identity coherence on all sheaf morphisms. -/
theorem directImageComp_id_source (f : Z ⟶ X) (F : Sheaf Z.smallEtaleTopology A) :
    (directImage f A).map ((directImageId A Z).inv.app F) ≫
        (directImageComp A f (𝟙 Z)).hom.app F =
      (directImageCongr A (Category.id_comp f)).inv.app F := by
  apply Sheaf.hom_ext
  ext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    directImage_map_app, directImageId_inv_app_hom_app,
    directImageComp_hom_app_hom_app, directImageCongr_inv_app_hom_app]
  change F.obj.map ((etaleObjectPullbackId Z).hom.app
      ((etaleObjectPullback f).obj U.unop)).op ≫
    F.obj.map ((etaleObjectPullbackComp f (𝟙 Z)).hom.app U.unop).op =
    F.obj.map ((etaleObjectPullbackCongr (Category.id_comp f)).hom.app U.unop).op
  rw [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact etaleObjectPullbackComp_id_source f U.unop

/-- The two triple-composition routes agree, including the canonical comparison
for associativity of the base morphisms. -/
theorem directImageComp_assoc (f : Z ⟶ X) (g : V ⟶ Z) (h : W ⟶ V)
    (F : Sheaf W.smallEtaleTopology A) :
    (directImage f A).map ((directImageComp A g h).hom.app F) ≫
        (directImageComp A f (h ≫ g)).hom.app F =
      (directImageComp A f g).hom.app ((directImage h A).obj F) ≫
        (directImageComp A (g ≫ f) h).hom.app F ≫
        (directImageCongr A (Category.assoc h g f)).inv.app F := by
  apply Sheaf.hom_ext
  ext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    directImage_map_app, directImageComp_hom_app_hom_app,
    directImageCongr_inv_app_hom_app]
  change F.obj.map ((etaleObjectPullbackComp g h).hom.app
      ((etaleObjectPullback f).obj U.unop)).op ≫
    F.obj.map ((etaleObjectPullbackComp f (h ≫ g)).hom.app U.unop).op =
    F.obj.map ((etaleObjectPullback h).map
      ((etaleObjectPullbackComp f g).hom.app U.unop)).op ≫
    F.obj.map ((etaleObjectPullbackComp (g ≫ f) h).hom.app U.unop).op ≫
    F.obj.map ((etaleObjectPullbackCongr (Category.assoc h g f)).hom.app U.unop).op
  simp only [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact etaleObjectPullbackComp_assoc f g h U.unop

end Langlands.Geometry.EtaleDirectImage

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry
open EtaleDirectImage

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]

/-- The constructed identity inverse image, adjoint to the actual identity
functor via the geometric direct-image comparison. -/
def inverseImageIdentityAdjunction (X : Scheme.{u}) :
    inverseImage (𝟙 X) R ⊣ 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  (inverseImageAdjunction (𝟙 X) R).ofNatIsoRight (directImageId (ModuleCat.{u} R) X)

/-- The identity comparison is determined by the actual adjunctions. -/
def inverseImageId (X : Scheme.{u}) :
    inverseImage (𝟙 X) R ≅ 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  Adjunction.leftAdjointUniq (inverseImageIdentityAdjunction R X) Adjunction.id

/-- The identity comparison satisfies the actual identity-adjunction unit law. -/
@[reassoc (attr := simp)] theorem inverseImageId_unit (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageIdentityAdjunction R X).unit.app F ≫
        (inverseImageId R X).hom.app F = 𝟙 F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- Equal base maps give the comparison determined by geometric direct-image
equality transport and the constructed adjunctions. -/
def inverseImageCongr {f k : Z ⟶ X} (e : f = k) :
    inverseImage f R ≅ inverseImage k R :=
  Adjunction.leftAdjointUniq
    ((inverseImageAdjunction f R).ofNatIsoRight (directImageCongr (ModuleCat.{u} R) e))
    (inverseImageAdjunction k R)

/-- Successive constructed inverse images are left adjoint to geometric
direct image along the composite. -/
def inverseImageCompositeAdjunction (f : Z ⟶ X) (g : V ⟶ Z) :
    inverseImage f R ⋙ inverseImage g R ⊣ directImage (g ≫ f) (ModuleCat.{u} R) :=
  ((inverseImageAdjunction f R).comp (inverseImageAdjunction g R)).ofNatIsoRight
    (directImageComp (ModuleCat.{u} R) f g)

/-- The composition comparison is determined by the actual composite adjunction. -/
def inverseImageComp (f : Z ⟶ X) (g : V ⟶ Z) :
    inverseImage f R ⋙ inverseImage g R ≅ inverseImage (g ≫ f) R :=
  Adjunction.leftAdjointUniq (inverseImageCompositeAdjunction R f g)
    (inverseImageAdjunction (g ≫ f) R)

/-- The composition comparison intertwines the two adjunction units. -/
@[reassoc (attr := simp)] theorem inverseImageComp_unit (f : Z ⟶ X) (g : V ⟶ Z)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageCompositeAdjunction R f g).unit.app F ≫
        (directImage (g ≫ f) (ModuleCat.{u} R)).map ((inverseImageComp R f g).hom.app F) =
      (inverseImageAdjunction (g ≫ f) R).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The same composition comparison intertwines the two counits. -/
@[reassoc (attr := simp)] theorem inverseImageComp_counit (f : Z ⟶ X) (g : V ⟶ Z)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageComp R f g).hom.app
        ((directImage (g ≫ f) (ModuleCat.{u} R)).obj F) ≫
      (inverseImageAdjunction (g ≫ f) R).counit.app F =
    (inverseImageCompositeAdjunction R f g).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

end Langlands.Geometry.EtaleInverseImage
