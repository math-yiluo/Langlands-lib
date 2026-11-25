/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionTotalOplaxComparisonData
import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorData

/-! # Normalized section comparisons on cochain complexes

Source: Stacks Project, Cohomology on Sites, Tags 06YU and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] ordinaryTensorComparison ordinaryUnitComparison
  Mod.monoidalCategoryStruct Mod.inducingFunctorData SheafOfModules.monoidalCategory
  InternalAbelianSheafModule.sectionModuleEquivalence

private theorem ordinaryTotalTensor (T : Scheme.{u})
    [(equivalence Λ T).functor.Monoidal]
    (hd : ∀ M N : internalModules Λ T,
      Functor.OplaxMonoidal.δ (equivalence Λ T).functor M N =
        (ordinaryTensorComparison Λ T M N).hom)
    (A B : CochainComplex (internalModules Λ T) ℤ) :
    Functor.OplaxMonoidal.δ
      ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)) A B =
        (cochainTensorComparison Λ T A B).hom := by
  have hnat : Functor.OplaxMonoidal.δNatTrans (equivalence Λ T).functor =
      sectionOrdinaryTensorMap Λ T := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    simpa only [Functor.OplaxMonoidal.δNatTrans_app_app,
      sectionOrdinaryTensorMap_app] using hd M N
  unfold cochainTensorComparison
  calc
    _ = sectionTotalComparison Λ T A B := by
      unfold sectionTotalComparison
      exact congrArg (fun n ↦ HomologicalComplex.mapBifunctorComparison n (.up ℤ) A B) hnat
    _ = _ := sectionTotalComparison_eq Λ T A B

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem ordinaryTotalUnit (T : Scheme.{u})
    [(equivalence Λ T).functor.Monoidal]
    (hη : Functor.OplaxMonoidal.η (equivalence Λ T).functor =
      (ordinaryUnitComparison Λ T).hom) :
    Functor.OplaxMonoidal.η
      ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)) =
        (totalUnitComparison Λ T).hom := by
  simpa only [Functor.mapCochainComplexεIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Functor.Monoidal.εIso_inv, hη, totalUnitComparison,
    Iso.trans_hom, Functor.mapIso_hom] using
    (Functor.mapCochainComplex_η (equivalence Λ T).functor)

/-- The induced cochain monoidal structure has the fixed normalized tensor and unit maps.
Source: Stacks Project, Cohomology on Sites, Tags 06YU and 07A4.

Proof: the ordinary oplax tensor natural transformation equals sectionOrdinaryTensorMap
because all its components equal the normalized ordinary tensor comparison. Apply
mapBifunctorComparison to this equality and use sectionTotalComparison_eq to identify
its totalization with cochainTensorComparison. The cochain oplax unit is the inverse
of mapCochainComplexεIso. Its explicit single-complex formula, with the normalized
ordinary unit substituted, is exactly totalUnitComparison. No flatness is needed.
(auxiliary; not a blueprint node). -/
theorem section_cochain_monoidal_constraints (T : Scheme.{u})
    [(equivalence Λ T).functor.Monoidal]
    (hd : ∀ M N : internalModules Λ T,
      Functor.OplaxMonoidal.δ (equivalence Λ T).functor M N =
        (ordinaryTensorComparison Λ T M N).hom)
    (hη : Functor.OplaxMonoidal.η (equivalence Λ T).functor =
      (ordinaryUnitComparison Λ T).hom) :
    (∀ A B : CochainComplex (internalModules Λ T) ℤ,
      Functor.OplaxMonoidal.δ
        ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)) A B =
          (cochainTensorComparison Λ T A B).hom) ∧
    (Functor.OplaxMonoidal.η
      ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)) =
        (totalUnitComparison Λ T).hom) := by
  exact ⟨ordinaryTotalTensor Λ T hd, ordinaryTotalUnit Λ T hη⟩

end AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints
