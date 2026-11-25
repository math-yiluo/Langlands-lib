/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel

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

/-- Sectionwise direct-image/restriction comparison before deriving.
Source: Stacks Tag 08FE (blueprint: def-pc-mayer-vietoris-image-chain-data). -/
abbrev schemeMVRestrictionImageIso {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens) :
    RingedSpace.moduleDirectImage h.toLRSHom.toShHom ⋙ schemeOpenRestriction Y W ≅
      schemeOpenRestriction X (h ⁻¹ᵁ W) ⋙ Scheme.Modules.pushforward (h ∣_ W) :=
  schemeMVUnderivedOpenRestriction h W

/-- Pushforward commutes with restriction followed by open direct image.
All factors are constructed sectionwise; no existence witness is selected.
Source: Stacks Tag 08FE (blueprint: def-pc-mayer-vietoris-image-chain-data). -/
def schemeMVImageIso {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens) :
    schemeOpenModuleImage X (h ⁻¹ᵁ W) ⋙ RingedSpace.moduleDirectImage h.toLRSHom.toShHom ≅
      RingedSpace.moduleDirectImage h.toLRSHom.toShHom ⋙ schemeOpenModuleImage Y W :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pushforwardComp (h ⁻¹ᵁ W).ι h ≪≫
        eqToIso (congrArg Scheme.Modules.pushforward (morphismRestrict_ι h W).symm) ≪≫
        (Scheme.Modules.pushforwardComp (h ∣_ W) W.ι).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (schemeMVRestrictionImageIso h W).symm _ ≪≫
    Functor.associator _ _ _

/-- Termwise sectionwise comparison followed by open restriction of the chain map.
Source: Stacks Tags 08FE and 08BV
(blueprint: def-pc-mayer-vietoris-image-chain-data). -/
def schemeMVImageComponent {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj
      (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ⟶
        schemeOpenModuleImageComplex Y W J :=
  { f := fun n ↦ (schemeMVImageIso h W).hom.app (I.X n) ≫
      (schemeOpenModuleImage Y W).map (f.f n)
    comm' := by
      intro i j hij
      have hn := (schemeMVImageIso h W).hom.naturality (I.d i j)
      change (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
          ((schemeOpenModuleImage X (h ⁻¹ᵁ W)).map (I.d i j)) ≫
          (schemeMVImageIso h W).hom.app (I.X j) =
        (schemeMVImageIso h W).hom.app (I.X i) ≫
          (schemeOpenModuleImage Y W).map
            ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map (I.d i j)) at hn
      change ((schemeMVImageIso h W).hom.app (I.X i) ≫
        (schemeOpenModuleImage Y W).map (f.f i)) ≫
          (schemeOpenModuleImage Y W).map (J.d i j) =
        (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).map
            ((schemeOpenModuleImage X (h ⁻¹ᵁ W)).map (I.d i j)) ≫
          ((schemeMVImageIso h W).hom.app (I.X j) ≫
            (schemeOpenModuleImage Y W).map (f.f j))
      rw [Category.assoc, ← Functor.map_comp, f.comm i j, Functor.map_comp]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ (schemeOpenModuleImage Y W).map (f.f j)) hn.symm).trans
          (Category.assoc _ _ _)) }

/-- The right-derived unit transported from homotopy categories to complexes.
It is defined on every complex, without a K-injectivity assumption.
Source: Stacks Tag 079V (blueprint: def-pc-mayer-vietoris-image-chain-data). -/
def schemeMVDirectImageLocalization {X Y : Scheme.{u}} (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ schemeDerivedDirectImage h :=
  (Functor.isoWhiskerLeft
    ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.isoWhiskerRight
    ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomotopyCategoryFactors (.up ℤ))
    DerivedCategory.Qh).inv ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _)
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerivedFunctorUnit ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    (schemeDerivedDirectImage h)).hom

/-- Localization comparison for restriction followed by open direct image,
including on complexes that are not K-injective.
Source: Stacks Tags 079V and 08BV (blueprint: def-pc-mayer-vietoris-image-chain-data). -/
def schemeMVOpenImageLocalization (X : Scheme.{u}) (W : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (schemeOpenModuleImageComplex X W K) ⟶
      ((schemeMVDerivedRestriction X W) ⋙ schemeDerivedDirectImage W.ι).obj
        (DerivedCategory.Q.obj K) :=
  (schemeMVDirectImageLocalization W.ι).app
      (((schemeOpenRestriction X W).mapHomologicalComplex (.up ℤ)).obj K) ≫
    (schemeDerivedDirectImage W.ι).map
      ((schemeOpenRestriction X W).mapDerivedCategoryFactors.inv.app K)

/-- On a K-injective complex the transported unit is the inverse computation iso.
Source: Stacks Tag 079V (blueprint: def-pc-mayer-vietoris-image-chain-data). -/
theorem schemeMVDirectImageLocalization_app {X Y : Scheme.{u}} (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [K.IsKInjective] :
    (schemeMVDirectImageLocalization h).app K =
      (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom K).inv := by
  simp [schemeMVDirectImageLocalization, RingedSpace.derivedModuleDirectImageKInjectiveIso]

/-- The general localization comparison agrees with the canonical comparison on
K-injectives. Source: Stacks Tag 08BV
(blueprint: def-pc-mayer-vietoris-image-chain-data). -/
theorem schemeMVOpenImageLocalization_eq (X : Scheme.{u}) (W : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [K.IsKInjective] :
    schemeMVOpenImageLocalization X W K =
      (schemeOpenModuleImageComplexComparison X W K (schemeMVAdjunction X W)).hom := by
  have := isKInjective_schemeOpenRestriction X W K
  rw [schemeMVOpenImageLocalization, schemeMVDirectImageLocalization_app]
  simp [schemeOpenModuleImageComplexComparison, schemeMVAdjunction,
    RingedSpace.derivedModuleDirectImageKInjectiveIso, Functor.rightDerivedFunctorObjQIso,
    Functor.mapHomotopyCategoryFactors]

/-- Naturality of the general open-image localization comparison.
Source: Stacks Tag 08BV (blueprint: def-pc-mayer-vietoris-image-chain-data). -/
theorem schemeMVOpenImageLocalization_naturality (X : Scheme.{u}) (W : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (f : K ⟶ L) :
    DerivedCategory.Q.map
        (((schemeOpenModuleImage X W).mapHomologicalComplex (.up ℤ)).map f) ≫
      schemeMVOpenImageLocalization X W L =
    schemeMVOpenImageLocalization X W K ≫
      ((schemeMVDerivedRestriction X W) ⋙ schemeDerivedDirectImage W.ι).map
        (DerivedCategory.Q.map f) := by
  let r := (schemeOpenRestriction X W).mapHomologicalComplex (.up ℤ)
  have hn := (schemeMVDirectImageLocalization W.ι).naturality (r.map f)
  have hf := (schemeOpenRestriction X W).mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn hf
  dsimp only [schemeMVOpenImageLocalization, Functor.comp_map]
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, ← Functor.map_comp]
  erw [hf]
  rw [Functor.map_comp, Category.assoc]

/-- Factorization of each explicit component into the sectionwise comparison
and the open-image functor applied to f. Source: Stacks Tag 08FE
(blueprint: def-pc-mayer-vietoris-image-chain-data). -/
theorem schemeMVImageComponent_factor {X Y : Scheme.{u}} (h : X ⟶ Y) (W : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    schemeMVImageComponent h W I J f =
      schemeMVImageComponent h W I _ (𝟙 _) ≫
        ((schemeOpenModuleImage Y W).mapHomologicalComplex (.up ℤ)).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (schemeMVImageIso h W).hom.app (I.X n) ≫
      (schemeOpenModuleImage Y W).map (f.f n) =
    ((schemeMVImageIso h W).hom.app (I.X n) ≫
      (schemeOpenModuleImage Y W).map (𝟙 _)) ≫
        (schemeOpenModuleImage Y W).map (f.f n)
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry
