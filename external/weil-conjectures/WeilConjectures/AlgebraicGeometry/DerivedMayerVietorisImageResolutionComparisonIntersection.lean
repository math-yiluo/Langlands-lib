/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
import WeilConjectures.AlgebraicGeometry.MayerVietorisImageLocalizationCompatibility
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

private theorem image_resolution_normalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {I E : C} {A B : D} (e : I ≅ E) (a : F.obj I ≅ A) (b : B ≅ F.obj E)
    (f : A ⟶ B) (hf : a.hom ≫ f ≫ b.hom = F.map e.hom) :
    F.map e.inv ≫ a.hom ≫ f = b.inv := by
  apply (cancel_mono b.hom).mp
  rw [Category.assoc, Category.assoc, hf, ← F.map_comp, e.inv_hom_id, F.map_id,
    b.inv_hom_id]

private theorem image_resolution_comparison_of_localization
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (H : E ⥤ D)
    {M N O : C} {A B : D} {I J K : E}
    {m : M ⟶ N} {n : N ⟶ O} {k : M ⟶ O} {s : A ⟶ B} {d : B ⟶ Q.obj M}
    {r : I ⟶ J} {t : J ⟶ K} {v : I ⟶ K} {c : Q.obj O ≅ H.obj K}
    {l : Q.obj N ⟶ H.obj J} {x : A ⟶ H.obj I}
    (hfactor : k = m ≫ n) (hnat : Q.map n ≫ c.hom = l ≫ H.map t)
    (hl : s ≫ d ≫ Q.map m ≫ l = x ≫ H.map r) (hn : r ≫ t = v) :
    s ≫ d ≫ Q.map k = x ≫ H.map v ≫ c.inv := by
  apply (cancel_mono c.hom).mp
  simp only [hfactor, Q.map_comp, Category.assoc, c.inv_hom_id, Category.comp_id]
  rw [hnat, reassoc_of% hl, ← H.map_comp, hn]

/-- The restriction-induced intersection component realizes the canonical derived comparison.
Source: Stacks Project, Tags 08FE, 08BV and 0D5T.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison-intersection).

Proof: Factor the constructed third component into the sectionwise isomorphism and
open image of f. Postcompose by the target open-image computation isomorphism,
which is invertible. Naturality of the general localization map moves f across
that map. The source-only localization compatibility identifies the remaining
source composite with the canonical derived open comparison. The normalization
of f, after cancelling the target resolution isomorphism and applying the inverse
source resolution isomorphism, supplies the final equality. -/
theorem schemeMV_image_resolution_comparison_intersection
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
        schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
    (hf : (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map f ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let m := schemeMVImageChainMap (h := h) U V I J f
    (schemeDerivedDirectImage h).map
        (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
            schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
            (schemeMVResolutionIso X E).inv ≫
          (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
            (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv) ≫
        (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
          (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I)).hom ≫
        DerivedCategory.Q.map m.τ₃ =
      (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
        (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
            schemeDerivedDirectImage (U ⊓ V).ι).map
            (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
          (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
            (schemeMVAdjunction Y (U ⊓ V))).inv) := by
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let H := (schemeMVDerivedRestriction Y (U ⊓ V)) ⋙ schemeDerivedDirectImage (U ⊓ V).ι
  let a := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I
  let b := schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)
  let c := schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
    (schemeMVAdjunction Y (U ⊓ V))
  have hn : (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).inv ≫
      a.hom ≫ DerivedCategory.Q.map f = b.inv := by
    exact image_resolution_normalization (schemeDerivedDirectImage h)
      (schemeMVResolutionIso X E) a b (DerivedCategory.Q.map f) hf
  have hp : h ⁻¹ᵁ (U ⊓ V) = (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) := rfl
  have : (schemeOpenModuleImageComplex X (h ⁻¹ᵁ (U ⊓ V)) I).IsKInjective := by
    rw [hp]
    infer_instance
  have hl := schemeMV_image_localization_compatibility X Y h (U ⊓ V) I E
    (schemeMVResolutionIso X E)
  have hnat := schemeMVOpenImageLocalization_naturality Y (U ⊓ V) f
  rw [schemeMVOpenImageLocalization_eq Y (U ⊓ V) J] at hnat
  dsimp only at hl hnat
  exact image_resolution_comparison_of_localization DerivedCategory.Q H (c := c)
    (schemeMVImageComponent_factor h (U ⊓ V) I J f) hnat hl
    ((Category.assoc _ _ _).trans hn)

end AlgebraicGeometry
