/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData

/-! # Factoring the complex image component

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-image-component-composition-factor).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
attribute [local irreducible] schemeMVImageIso schemeMVUnderivedOpenRestriction
  schemeMVUnderivedOpenComposition schemeOpenModuleAdjunction schemeMVImageComponent

private theorem pushforwardCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g) :
    Scheme.Modules.pushforwardCongr hf = eqToIso (congrArg Scheme.Modules.pushforward hf) := by
  subst g
  ext M T a
  simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Scheme.Modules.Hom.id_app]
  simp

private theorem image_factor
    {C A D B : Type*} [Category C] [Category A] [Category D] [Category B]
    (LX : C ⥤ A) (RX : A ⥤ C) (LY : D ⥤ B)
    (F : C ⥤ D) (G : A ⥤ B) (R : B ⥤ D)
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ R) (M : C) :
    ((Functor.associator LX RX F ≪≫ Functor.isoWhiskerLeft LX β ≪≫
        (Functor.associator LX G R).symm ≪≫ Functor.isoWhiskerRight α.symm R ≪≫
        Functor.associator F LY R).hom.app M) ≫ R.map (α.hom.app M) =
      β.hom.app (LX.obj M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact CategoryTheory.Category.comp_id _

/-- The image isomorphism cancels with the restriction isomorphism.
Source: Stacks Project, Tag 08FE.
Proof: expand the associators and whiskering defining the image isomorphism.
Equality induction identifies pushforwardCongr with eqToIso. The remaining two
restriction factors cancel by functoriality and the inverse-hom identity.
No cover or nonempty-open assumption is involved.
(blueprint: lem-pc-mayer-vietoris-image-component-composition-factor). -/
theorem schemeMVImageIso_composition_factor
    {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (schemeMVImageIso h W).hom.app M ≫
      (RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom).map
        ((schemeMVUnderivedOpenRestriction h W).hom.app M) =
    (schemeMVUnderivedOpenComposition h W).hom.app
      ((schemeOpenRestriction X (h ⁻¹ᵁ W)).obj M) := by
  have he : schemeMVImageIso h W =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (schemeOpenRestriction X (h ⁻¹ᵁ W))
          (schemeMVUnderivedOpenComposition h W) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (schemeMVUnderivedOpenRestriction h W).symm
          (RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom) ≪≫
        Functor.associator _ _ _ := by
    unfold schemeMVImageIso schemeMVUnderivedOpenComposition
    rw [pushforwardCongr_eq]
    rfl
  rw [he]
  exact image_factor (schemeOpenRestriction X (h ⁻¹ᵁ W))
    (RingedSpace.moduleDirectImage (h ⁻¹ᵁ W).ι.toLRSHom.toShHom)
    (schemeOpenRestriction Y W) (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom)
    (schemeMVUnderivedOpenRestriction h W) (schemeMVUnderivedOpenComposition h W) M

end AlgebraicGeometry
