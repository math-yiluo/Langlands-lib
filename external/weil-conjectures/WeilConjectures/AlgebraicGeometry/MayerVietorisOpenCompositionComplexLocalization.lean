/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionNormalization

/-! # The complex form of the open composition unit equation

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-open-composition-complex-localization).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

private lemma schemeMV_localization_unit_app
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (schemeMVDirectImageLocalization h).app I =
      (DerivedCategory.quotientCompQhIso _).inv.app
          (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
        (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj I) ≫
        (schemeDerivedDirectImage h).map
          ((DerivedCategory.quotientCompQhIso _).hom.app I) := by
  dsimp only [schemeMVDirectImageLocalization, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]

-- Cancel the quotient comparisons before specializing to derived categories of modules.
private lemma schemeMV_transport_composition_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : B ⥤ D) (RX : A ⥤ B) (G : A ⥤ C) (RY : C ⥤ D)
    (β : RX ⋙ F ≅ G ⋙ RY)
    {U₀ U₁ : A} {X₀ X₁ : B} {V₀ V₁ : C} {Y₀ Y₁ Z₀ Z₁ : D}
    (e : U₀ ≅ U₁) (ex : X₀ ≅ X₁) (ev : V₀ ≅ V₁)
    (ey : Y₀ ≅ Y₁) (ez : Z₀ ≅ Z₁)
    (ux : X₀ ⟶ RX.obj U₀) (uf : Y₀ ⟶ F.obj X₀)
    (ug : V₀ ⟶ G.obj U₀) (uy : Z₀ ⟶ RY.obj V₀)
    (b : Y₁ ⟶ Z₁) (bh : Y₀ ⟶ Z₀)
    (hb : b ≫ ez.inv = ey.inv ≫ bh)
    (hn : uf ≫ F.map ux ≫ β.hom.app U₀ = bh ≫ uy ≫ RY.map ug) :
    (ey.inv ≫ uf ≫ F.map ex.hom) ≫
        F.map (ex.inv ≫ ux ≫ RX.map e.hom) ≫ β.hom.app U₁ =
      b ≫ (ez.inv ≫ uy ≫ RY.map ev.hom) ≫
        RY.map (ev.inv ≫ ug ≫ G.map e.hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, ex.hom_inv_id, F.map_id, Category.id_comp]
  rw [← RY.map_comp_assoc, ev.hom_inv_id, RY.map_id, Category.id_comp]
  have hβ := β.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hβ
  rw [hβ, reassoc_of% hb]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun t ↦ ey.inv ≫ t ≫ RY.map (G.map e.hom)) hn

/-- The open composition unit equation on any complex on the inverse-image open.
Source: Stacks Project, Tags 08FE and 0D5T.
Proof: apply schemeMVOpenComposition_unit_normalization to the homotopy quotient of J.
The components of mapHomotopyCategoryFactors and quotientCompQhIso are identities.
Expand schemeMVDirectImageLocalization and use those component identities to identify
its units with the homotopy units. The homotopy composition comparison is the quotient
of the displayed complex comparison, by mapHomotopyCategoryCompIso. Functoriality of Q
and the naturality of the quotient comparison give the displayed equation. There is
no restriction factor, counit, or K-injectivity hypothesis. This applies also to the
empty open, full open, and identity h because the same quotient identities apply.
(blueprint: lem-pc-mayer-vietoris-open-composition-complex-localization). -/
theorem schemeMVOpenComposition_complex_localization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ W).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ W) ⋙ schemeDerivedDirectImage W.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ W) W.ι)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ W).toScheme.toRingedSpace)) ℤ) :
    let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ W).ι.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
    let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
    let b₀ := (Functor.mapHomologicalComplexCompIso
        (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
    (schemeMVDirectImageLocalization h).app
        ((RX.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage h).map
        ((schemeMVDirectImageLocalization (h ⁻¹ᵁ W).ι).app J) ≫
      β.hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map b₀ ≫
      (schemeMVDirectImageLocalization W.ι).app
        ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage W.ι).map
        ((schemeMVDirectImageLocalization (h ∣_ W)).app J) := by
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ W).ι.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
  let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
  have hn := schemeMVOpenComposition_unit_normalization X Y h W β hβ
    ((HomotopyCategory.quotient _ (.up ℤ)).obj J)
  let b₀ := (Functor.mapHomologicalComplexCompIso
      (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
  have hb : (schemeMVHomotopyOpenComposition h W).hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj J) =
      (HomotopyCategory.quotient _ (.up ℤ)).map b₀ := by
    dsimp [b₀, schemeMVHomotopyOpenComposition, Functor.mapHomotopyCategoryCompIso,
      Quotient.natIsoLift, Quotient.natTransLift]
    rw [Functor.map_comp]
    rfl
  dsimp only at hn ⊢
  rw [hb] at hn
  simp only [schemeMV_localization_unit_app]
  exact schemeMV_transport_composition_unit
    (schemeDerivedDirectImage h) (schemeDerivedDirectImage (h ⁻¹ᵁ W).ι)
    (schemeDerivedDirectImage (h ∣_ W)) (schemeDerivedDirectImage W.ι) β
    ((DerivedCategory.quotientCompQhIso _).app J)
    ((DerivedCategory.quotientCompQhIso _).app ((RX.mapHomologicalComplex (.up ℤ)).obj J))
    ((DerivedCategory.quotientCompQhIso _).app ((G.mapHomologicalComplex (.up ℤ)).obj J))
    ((DerivedCategory.quotientCompQhIso _).app
      ((F.mapHomologicalComplex (.up ℤ)).obj ((RX.mapHomologicalComplex (.up ℤ)).obj J)))
    ((DerivedCategory.quotientCompQhIso _).app
      ((RY.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj J)))
    _ _ _ _ _ _ (DerivedCategory.quotientCompQhIso_inv_naturality b₀) hn

end AlgebraicGeometry
