/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback

public import WeilConjectures.AlgebraicGeometry.Structure.StructureDerivedImageCohomologyEquivalences
public import WeilConjectures.AlgebraicGeometry.Structure.StructureDerivedImageCohomologyCompatibility

/-! # Naturality of affine-base sections of a structure-module direct image

Source: Stacks Project, Tags 01XK, 01FB and 03FD.
(blueprint: new-structure-derived-image-cohomology-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The source comparison for the structure-module direct image over an affine base:
the inverse affine Leray equivalence followed by the module-to-abelian comparison. -/
noncomputable def structureDerivedImageCohomologyEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{v}} [IsAffine T] (q : X ⟶ T) [IsProper q] :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1 ⋙
          SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)).obj
        ((schemeDerivedDirectImage q).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)))) ≃+
      Sheaf.H (structureSheafAb X) 1 :=
  (affineLerayEquiv q).symm.trans (structureModuleAbelianEquiv X)

/-- The target comparison for a factorisation `j ≫ q = qY` over an affine base: the
target affine Leray equivalence followed by the module-to-abelian comparison. -/
noncomputable def structureDerivedImageCohomologyTargetEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X Y : Scheme.{v}} [IsAffine T] (q : X ⟶ T) (j : Y ⟶ X) {qY : Y ⟶ T} [IsProper qY]
    (hj : j ≫ q = qY) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1 ⋙
          SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)).obj
        ((schemeDerivedDirectImage qY).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)))) ≃+
      Sheaf.H (structureSheafAb Y) 1 :=
  (affineLerayTargetEquiv q j hj).trans (structureModuleAbelianEquiv Y)

-- Composing the module and abelian comparisons requires large category transports.
/-- The affine-base Leray comparisons `structureDerivedImageCohomologyEquiv q` and
`structureDerivedImageCohomologyTargetEquiv q j hj` for structure modules respect a map
`j` of total spaces.
Source: Stacks Project, Tag 01XK, lemma-quasi-coherence-higher-direct-images-application;
Tag 01FB, remark-explain-arrow; Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: new-structure-derived-image-cohomology-naturality)

Proof: By `structure_derived_image_module_naturality`, the affine Leray edges carry `H(b)`
to the module h-map of the structure map of `j`. By `structure_module_abelian_comparison`,
the fixed injective-resolution comparison carries the module h-map of every scheme
morphism to `structureSheafCohomologyPullback`. Applying the two squares in turn gives
the equation. -/
theorem structure_derived_image_cohomology_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X Y : Scheme.{v}} [IsAffine T] (q : X ⟶ T) [IsProper q]
    (j : Y ⟶ X) {qY : Y ⟶ T} [IsProper qY] (hj : j ≫ q = qY) :
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings X.toRingedSpace)) 0).obj
        (SheafOfModules.unit X.ringCatSheaf)
    let AY := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1 ⋙
      SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)
    let b := relativeMVUnit j q A ≫
      (schemeDerivedDirectImage (j ≫ q)).map
        (Modules.canonicalSinglePullbackMap j (SheafOfModules.unit X.ringCatSheaf) ≫
          (DerivedCategory.singleFunctor _ 0).map (Modules.pullbackObjUnitIso j).hom) ≫
      eqToHom (congrArg (fun t ↦ (schemeDerivedDirectImage t).obj AY) hj)
    ∀ z, structureDerivedImageCohomologyTargetEquiv q j hj (H.map b z) =
      structureSheafCohomologyPullback j 1 (structureDerivedImageCohomologyEquiv q z) := by
  classical
  intro A AY H b z
  change structureModuleAbelianEquiv Y (affineLerayTargetEquiv q j hj (H.map b z)) =
    structureSheafCohomologyPullback j 1
      (structureModuleAbelianEquiv X ((affineLerayEquiv q).symm z))
  rw [structure_derived_image_module_naturality q j hj z]
  exact structure_module_abelian_comparison j _

end AlgebraicGeometry.Scheme
