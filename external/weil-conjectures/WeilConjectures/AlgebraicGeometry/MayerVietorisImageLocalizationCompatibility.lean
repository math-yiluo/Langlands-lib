/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.MayerVietorisImageCompositionLocalization
import WeilConjectures.AlgebraicGeometry.MayerVietorisImageRestrictionLocalization

/-! # Explicit restriction-induced comparison maps

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-image-chain-data).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

private theorem comparison_naturality
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    (L : C ⥤ A) (R : A ⥤ C) (F : C ⥤ D) (G : A ⥤ B) (S : B ⥤ D) (T : D ⥤ B)
    (β : R ⋙ F ≅ G ⋙ S) (α : F ⋙ T ≅ L ⋙ G) {E E' : C} (f : E ⟶ E') :
    F.map ((L ⋙ R).map f) ≫
        (β.app (L.obj E') ≪≫ S.mapIso (α.symm.app E')).hom =
      (β.app (L.obj E) ≪≫ S.mapIso (α.symm.app E)).hom ≫
        (T ⋙ S).map (F.map f) := by
  have hb := β.hom.naturality (L.map f)
  have ha := α.inv.naturality f
  dsimp only [Functor.comp_map] at hb ha
  dsimp only [Functor.comp_map, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, hb, Category.assoc, ← Functor.map_comp]
  rw [ha, Functor.map_comp, Category.assoc]

private theorem open_comparison_naturality
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    {E E' : schemeDerivedCategory X} (f : E ⟶ E') :
    (schemeDerivedDirectImage h).map
        (((schemeMVDerivedRestriction X (h ⁻¹ᵁ W)) ⋙
          schemeDerivedDirectImage (h ⁻¹ᵁ W).ι).map f) ≫
      (schemeMVOpenComparison h W E').hom =
    (schemeMVOpenComparison h W E).hom ≫
      (((schemeMVDerivedRestriction Y W) ⋙ schemeDerivedDirectImage W.ι).map
        ((schemeDerivedDirectImage h).map f)) := by
  exact comparison_naturality (schemeMVDerivedRestriction X (h ⁻¹ᵁ W))
    (schemeDerivedDirectImage (h ⁻¹ᵁ W).ι) (schemeDerivedDirectImage h)
    (schemeDerivedDirectImage (h ∣_ W)) (schemeDerivedDirectImage W.ι)
    (schemeMVDerivedRestriction Y W)
    ((schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ W) W.ι)
    (schemeMVOpenRestrictionComparison h W) f

private theorem image_unit_square
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let H := (schemeMVDerivedRestriction Y W) ⋙ schemeDerivedDirectImage W.ι
    (schemeMVDirectImageLocalization h).app (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ≫
        (schemeDerivedDirectImage h).map (schemeMVOpenImageLocalization X (h ⁻¹ᵁ W) I) ≫
        (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom =
      DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
        schemeMVOpenImageLocalization Y W (F.obj I) ≫
        H.map ((schemeMVDirectImageLocalization h).app I) := by
  have hc := schemeMV_image_composition_localization X Y h W I
  simpa only [schemeMV_image_restriction_localization X Y h W I, Functor.comp_map] using hc

/-- Compatibility of the sectionwise open-image comparison with localization.
This concerns only the sectionwise isomorphism on a source K-injective complex;
it contains no chosen map to a target resolution and no Mayer--Vietoris morphism.
Source: Stacks Tags 08FE, 079V and 0D5T.
(blueprint: lem-pc-mayer-vietoris-image-localization-compatibility).

Proof: The direct-image computation map is the inverse right-derived unit.
The comparison for the open image is the inverse right-derived unit on the
restricted complex, followed by the exact-restriction localization comparison.
The underived sectionwise isomorphism is the composite of pushforwardComp along
the open square and the restriction/direct-image isomorphism of Tag 08FE.
Apply the unit equations for rightDerivedFunctorCompMapDerivedCategoryIso,
rightDerivedFunctorNatIso and rightDerivedFunctorCompIso to these factors.
The resulting composite is the defining right-derived unit equation for
schemeMVDirectImageComposition and schemeMVOpenRestrictionComparison.
These equations determine the comparisons by the right-derived universal
property. Their composite therefore gives the stated square on I. Transport
along e by naturality of those comparisons gives the displayed equation.
No K-injectivity of h_*I is used: the comparison on that complex is the general
localization map, not an inverse computation isomorphism. -/
theorem schemeMV_image_localization_compatibility
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] [(schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I).IsKInjective]
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let H := (schemeMVDerivedRestriction Y W) ⋙ schemeDerivedDirectImage W.ι
    (schemeDerivedDirectImage h).map
        ((((schemeMVDerivedRestriction X (h ⁻¹ᵁ W)) ⋙
            schemeDerivedDirectImage (h ⁻¹ᵁ W).ι).map e.inv) ≫
          (schemeOpenModuleImageComplexComparison X (h ⁻¹ᵁ W) I
            (schemeMVAdjunction X (h ⁻¹ᵁ W))).inv) ≫
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I)).hom ≫
      DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) =
    (schemeMVOpenComparison h W E).hom ≫
      H.map ((schemeDerivedDirectImage h).map e.inv ≫
        (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I).hom) := by
  let D := schemeDerivedDirectImage h
  let HX := (schemeMVDerivedRestriction X (h ⁻¹ᵁ W)) ⋙
    schemeDerivedDirectImage (h ⁻¹ᵁ W).ι
  let HY := (schemeMVDerivedRestriction Y W) ⋙ schemeDerivedDirectImage W.ι
  let c := schemeOpenModuleImageComplexComparison X (h ⁻¹ᵁ W) I
    (schemeMVAdjunction X (h ⁻¹ᵁ W))
  let d := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I
  let d' := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
    (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I)
  have hs := image_unit_square X Y h W I
  rw [schemeMVDirectImageLocalization_app, schemeMVDirectImageLocalization_app,
    schemeMVOpenImageLocalization_eq] at hs
  have hb := congrArg (fun t ↦ D.map c.inv ≫ d'.hom ≫ t ≫ HY.map d.hom) hs
  have hbase : D.map c.inv ≫ d'.hom ≫
      DerivedCategory.Q.map (schemeMVImageComponent h W I _ (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W _ =
    (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom ≫ HY.map d.hom := by
    simp only [Category.assoc] at hb
    change (D.map c.inv ≫ d'.hom ≫ d'.inv ≫ D.map c.hom ≫
        (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom ≫ HY.map d.hom) =
      (D.map c.inv ≫ d'.hom ≫ DerivedCategory.Q.map
        (schemeMVImageComponent h W I _ (𝟙 _)) ≫
        schemeMVOpenImageLocalization Y W _ ≫ HY.map d.inv ≫ HY.map d.hom) at hb
    have hb' := hb.symm
    simp only [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp] at hb'
    erw [CategoryTheory.Category.comp_id] at hb'
    exact hb'
  have hn := open_comparison_naturality X Y h W e.inv
  dsimp only
  change D.map (HX.map e.inv ≫ c.inv) ≫ d'.hom ≫ _ ≫ _ =
    (schemeMVOpenComparison h W E).hom ≫ HY.map (D.map e.inv ≫ d.hom)
  rw [Functor.map_comp, Category.assoc, hbase, ← Category.assoc, hn,
    Category.assoc, ← Functor.map_comp]

end AlgebraicGeometry
