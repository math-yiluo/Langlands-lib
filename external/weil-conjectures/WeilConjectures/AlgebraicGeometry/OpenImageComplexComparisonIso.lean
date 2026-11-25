/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen

/-! # Explicit K-injective comparison for one open

Source: Stacks Project, Cohomology, Tags 08BS and 08BV.
(blueprint: def-pc-open-image-complex-comparison-iso).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- Open restriction, transported to the open subscheme, preserves K-injectivity.
Source: Stacks, Tag 08BS (lemma-restrict-K-injective-to-open).
Proof: restrict on the open site and then apply the exact additive equivalence.
(blueprint: def-pc-open-image-complex-comparison-iso). -/
theorem isKInjective_schemeOpenRestriction (X : Scheme.{u}) (U : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((schemeOpenRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have := kInjective_of_restrict_open X.toRingedSpace U I
  let F := (Scheme.Modules.overEquiv U).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  change CochainComplex.IsKInjective
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))
  infer_instance

set_option backward.isDefEq.respectTransparency true in
/-- A constructed comparison, normalized to the supplied derived adjunction.
Source: Stacks, Tag 08BV (lemma-exact-sequence-j-star), first proof paragraph.
The inverse K-injective computation is followed by exact-restriction localization
and the unique right-adjoint comparison from the derived underived adjunction.
No witness of an existence theorem is chosen.
(blueprint: def-pc-open-image-complex-comparison-iso). -/
def schemeOpenModuleImageComplexComparison (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι) :
    DerivedCategory.Q.obj (schemeOpenModuleImageComplex X U I) ≅
      (schemeDerivedDirectImage U.ι).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj (DerivedCategory.Q.obj I)) :=
  let L := schemeOpenRestriction X U
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : L ⊣ R := schemeOpenModuleAdjunction X U
  have : CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_schemeOpenRestriction X U I
  (R.rightDerivedFunctorObjQIso
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫
    R.rightDerivedFunctor.mapIso (L.mapDerivedCategoryFactors.app I).symm ≪≫
    (a.mapDerivedCategoryRightDerivedAdjunction.rightAdjointUniq adj).app _

end AlgebraicGeometry
