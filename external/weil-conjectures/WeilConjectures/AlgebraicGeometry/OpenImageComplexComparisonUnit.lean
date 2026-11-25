/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonIso

/-! # Unit compatibility for the explicit open comparison

Source: Stacks Project, Cohomology, Tags 08BS and 08BV.
(blueprint: lem-pc-open-image-complex-comparison-unit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem unit_compute
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (I : CochainComplex C ℤ)
    [CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)] :
    DerivedCategory.Q.map ((a.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app I) ≫
      (R.rightDerivedFunctorObjQIso
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app I) =
        a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj I) := by
  have h := (a.mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj I)
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    R.rightDerivedFunctor.map _ = _ at h
  rw [L.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  dsimp only [Functor.comp_obj] at h
  have hf : DerivedCategory.Qh.map
      ((L.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I) =
        𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
    change DerivedCategory.Qh.map (𝟙 _) = _
    exact DerivedCategory.Qh.map_id _
  rw [hf] at h
  simp only [Functor.map_comp, Category.comp_id] at h
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_inv, asIso_hom]
  simp only [Category.assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc, ← reassoc_of% h]
  simp only [← Functor.map_comp, Iso.app_hom, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app]
  erw [Category.comp_id]
  have hn := a.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app I)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The explicit comparison identifies the localized restriction unit with the
unit of the supplied derived adjunction.
Source: Stacks, Tag 08BV (lemma-exact-sequence-j-star), first proof paragraph.
Proof: apply the derived-unit factorization to the underived adjunction on the
homotopy categories. Transport along quotientCompQhIso and exact restriction's
localization comparison. Finally use unit_rightAdjointUniq_hom_app.
(blueprint: lem-pc-open-image-complex-comparison-unit). -/
theorem schemeOpenModuleImageComplexComparison_unit (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι) :
    DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I) ≫
        (schemeOpenModuleImageComplexComparison X U I adj).hom =
      adj.unit.app (DerivedCategory.Q.obj I) := by
  let L := schemeOpenRestriction X U
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : L ⊣ R := schemeOpenModuleAdjunction X U
  let d := a.mapDerivedCategoryRightDerivedAdjunction
  have : CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_schemeOpenRestriction X U I
  have hc := unit_compute a I
  have hu := congrArg (fun f => f ≫ (d.rightAdjointUniq adj).hom.app
    (L.mapDerivedCategory.obj (DerivedCategory.Q.obj I))) hc
  have hh := hu.trans (Adjunction.unit_rightAdjointUniq_hom_app d adj _)
  simpa only [schemeOpenModuleImageComplexComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using! hh

end AlgebraicGeometry
