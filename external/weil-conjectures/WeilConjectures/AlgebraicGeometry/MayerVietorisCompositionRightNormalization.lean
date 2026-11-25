/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain
import WeilConjectures.AlgebraicGeometry.MayerVietorisImageComponentCompositionFactor

/-! # Right-hand image normalization

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-composition-right-normalization).
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

-- Rewrite composed termwise objects before elaborating maps between their presentations.
private theorem complex_comp_obj
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C]
    (P : A ⥤ B) (S : B ⥤ C) [P.PreservesZeroMorphisms] [S.PreservesZeroMorphisms]
    (K : CochainComplex A ℤ) :
    ((P ⋙ S).mapHomologicalComplex (.up ℤ)).obj K =
      (S.mapHomologicalComplex (.up ℤ)).obj ((P.mapHomologicalComplex (.up ℤ)).obj K) := rfl

-- Keep inverse cancellation and naturality independent of concrete derived constructions.
private theorem normalize_right
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A B E H K L : C} {S T U : D}
    (d : A ≅ B) (a : B ⟶ E) (z : E ⟶ H) (k : H ⟶ K) (l : K ⟶ L)
    (p : S ⟶ T) (t : T ⟶ U) (s : S ⟶ U)
    (u : T ⟶ R.obj B) (v : U ⟶ R.obj E)
    (hf : p ≫ t = s) (hn : u ≫ R.map a = t ≫ v) :
    p ≫ (u ≫ R.map d.inv) ≫ R.map ((d.hom ≫ a ≫ z) ≫ k) ≫ R.map l =
      s ≫ v ≫ R.map (z ≫ k ≫ l) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc d.inv d.hom, d.inv_hom_id, R.map_id, Category.id_comp]
  rw [← Category.assoc u (R.map a), hn]
  simp only [Category.assoc]
  rw [← Category.assoc p t, hf]

-- Explicit complex and derived-category conversions need a larger elaboration budget.
/-- Right-hand image normalization to the complex-composition composite.
Source: Stacks Project, Tags 08FE, 0D5T and 079V.

Proof: Apply schemeMVImageIso_composition_factor in every degree. Extensionality of chain
maps identifies the image component followed by open direct image of the underived
restriction comparison with the complex composition comparison b₀. Apply Q. Naturality
of schemeMVDirectImageLocalization for that underived comparison moves it past the open
direct-image unit. Expand the restriction-localization chain and open-image localization
on Y; cancel the inverse and hom of the exact Y-restriction factor inside R. Associativity
and functoriality give the displayed three-map composite. This calculation uses no
h-localization unit and no derived composition isomorphism.
The argument applies to arbitrary complexes, empty and full opens, and identity morphisms:
only functoriality, naturality and inverse-isomorphism equations are used.
(blueprint: lem-pc-mayer-vietoris-composition-right-normalization). -/
theorem schemeMV_composition_right_normalization
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
    let R := schemeDerivedDirectImage W.ι
    DerivedCategory.Q.map (schemeMVImageComponent h W I (F.obj I) (𝟙 _)) ≫
      schemeMVOpenImageLocalization Y W (F.obj I) ≫
      R.map (schemeMVRestrictionLocalizationChain X Y h W I) ≫
      R.map ((schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I)) =
    (let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
     let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
     let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
     let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
     let b₀ := (Functor.mapHomologicalComplexCompIso
         (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
       (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
     DerivedCategory.Q.map b₀ ≫
       (schemeMVDirectImageLocalization W.ι).app
         ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
       R.map ((schemeMVDirectImageLocalization (h ∣_ W)).app J ≫
         (schemeDerivedDirectImage (h ∣_ W)).map
           (LX.mapDerivedCategoryFactors.inv.app I) ≫
         (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I))) := by
  let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
    (.up ℤ)
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let LY := schemeOpenRestriction Y W
  let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
  let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
  have : LX.Additive := schemeOpenRestriction_additive X (h ⁻¹ᵁ W)
  have : LY.Additive := schemeOpenRestriction_additive Y W
  have : LX.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive LX
  have : LY.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive LY
  have : G.PreservesZeroMorphisms := inferInstance
  have : RY.Additive := Functor.Additive.mk (by intros; rfl)
  have : RY.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive RY
  let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
  let R := schemeDerivedDirectImage W.ι
  let a : (LY.mapHomologicalComplex (.up ℤ)).obj (F.obj I) ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj J :=
    (NatTrans.mapHomologicalComplex (schemeMVUnderivedOpenRestriction h W).hom
    (.up ℤ)).app I
  let b : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ⟶
      (RY.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj J) :=
    (Functor.mapHomologicalComplexCompIso
      (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
  let e : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ⟶
      schemeOpenModuleImageComplex Y W (F.obj I) :=
    schemeMVImageComponent h W I (F.obj I) (𝟙 (F.obj I))
  let c : schemeOpenModuleImageComplex Y W (F.obj I) ⟶
      (RY.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj J) :=
    by
      change ((LY ⋙ RY).mapHomologicalComplex (.up ℤ)).obj (F.obj I) ⟶ _
      rw [complex_comp_obj]
      exact (RY.mapHomologicalComplex (.up ℤ)).map a
  have hf : e ≫ c = b := by
    apply HomologicalComplex.Hom.ext
    funext n
    unfold e schemeMVImageComponent
    change ((schemeMVImageIso h W).hom.app (I.X n) ≫
        (schemeOpenModuleImage Y W).map (𝟙 _)) ≫
        RY.map ((schemeMVUnderivedOpenRestriction h W).hom.app (I.X n)) =
      (schemeMVUnderivedOpenComposition h W).hom.app (LX.obj (I.X n))
    simp only [CategoryTheory.Functor.map_id]
    exact schemeMVImageIso_composition_factor h W (I.X n)
  have hn := (schemeMVDirectImageLocalization W.ι).naturality a
  dsimp only [Functor.comp_map] at hn
  have hq : DerivedCategory.Q.map e ≫ DerivedCategory.Q.map c =
      DerivedCategory.Q.map b := by
    rw [← Functor.map_comp, hf]
  dsimp only
  unfold schemeMVOpenImageLocalization schemeMVRestrictionLocalizationChain
  exact normalize_right R (LY.mapDerivedCategoryFactors.app (F.obj I))
    (DerivedCategory.Q.map a) ((schemeMVDirectImageLocalization (h ∣_ W)).app J)
    ((schemeDerivedDirectImage (h ∣_ W)).map (LX.mapDerivedCategoryFactors.inv.app I))
    ((schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I))
    (DerivedCategory.Q.map e) (DerivedCategory.Q.map c) (DerivedCategory.Q.map b)
    ((schemeMVDirectImageLocalization W.ι).app ((LY.mapHomologicalComplex (.up ℤ)).obj
      (F.obj I)))
    ((schemeMVDirectImageLocalization W.ι).app ((G.mapHomologicalComplex (.up ℤ)).obj J))
    hq hn.symm

end AlgebraicGeometry
