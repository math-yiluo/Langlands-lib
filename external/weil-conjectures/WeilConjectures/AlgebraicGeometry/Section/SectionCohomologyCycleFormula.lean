/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # The section cohomology comparison on cycles

## References

* Stacks Project, Tags 01E4, 01F4 and 01FB
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
private theorem homologyπ_mapHomologyIso_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := ShortComplex.LeftHomologyData.canonical S
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

private theorem mapHomologyIso_inv_homologyπ
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C) [F.PreservesLeftHomologyOf S] :
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  rw [← cancel_epi (S.mapCyclesIso F).hom, ← reassoc_of% (homologyπ_mapHomologyIso_hom F S),
    Iso.hom_inv_id_assoc]
  simp

private theorem adjoint_homology_comparison_cycles
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (U : D ⥤ C) [L.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [L.PreservesHomology] [PreservesFiniteLimits U] (adj : L ⊣ U)
    (S : ShortComplex D) :
    let P := S.map U
    let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
    P.homologyπ ≫ adj.homEquiv P.homology S.homology
        ((P.mapHomologyIso L).inv ≫ ShortComplex.homologyMap
          (S.mapNatTrans adj.counit)) = k ≫ U.map S.homologyπ := by
  dsimp only
  let P := S.map U
  let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel U)).inv
  have hk : k ≫ U.map S.iCycles = P.iCycles := by
    exact P.isoCyclesOfIsLimit_inv_ι _
  let φ : P.map L ⟶ S := S.mapNatTrans adj.counit
  have hc : (P.mapCyclesIso L).inv ≫ ShortComplex.cyclesMap φ =
      L.map k ≫ adj.counit.app S.cycles := by
    apply (cancel_mono S.iCycles).1
    rw [Category.assoc, ShortComplex.cyclesMap_i]
    change (P.mapCyclesIso L).inv ≫ (P.map L).iCycles ≫
      adj.counit.app S.X₂ = (L.map k ≫ adj.counit.app S.cycles) ≫ S.iCycles
    have hi : (P.mapCyclesIso L).inv ≫ (P.map L).iCycles = L.map P.iCycles := by
      rw [← ShortComplex.mapCyclesIso_hom_iCycles P L,
        Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hi]
    have hn := adj.counit.naturality S.iCycles
    change L.map (U.map S.iCycles) ≫ adj.counit.app S.X₂ =
      adj.counit.app S.cycles ≫ S.iCycles at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← L.map_comp, hk]
  apply (adj.homEquiv _ _).symm.injective
  rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply,
    adj.homEquiv_counit, L.map_comp, Category.assoc]
  change L.map P.homologyπ ≫ ((P.mapHomologyIso L).inv ≫
    ShortComplex.homologyMap φ) = L.map k ≫ L.map (U.map S.homologyπ) ≫
    adj.counit.app S.homology
  rw [← Category.assoc, mapHomologyIso_inv_homologyπ,
    Category.assoc, ShortComplex.homologyπ_naturality, ← Category.assoc, hc]
  have hn := adj.counit.naturality S.homologyπ
  change L.map (U.map S.homologyπ) ≫ adj.counit.app S.homology =
    adj.counit.app S.cycles ≫ S.homologyπ at hn
  simp only [hn, Category.assoc]

namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

-- The cycle and restriction calculations below follow the private proved calculations in
-- FlatUnitRawSections and TargetSectionClassRestriction, respectively.
-- The adjunction comparison crosses sheaf, presheaf, and evaluation homology objects.
/-- Evaluation of theta sends the homology class of a cycle to its sheaf cohomology class.
The cycle section is pinned by the inverse kernel comparison and exact evaluation.
-/
theorem section_comparison_cycles {Y : Scheme.{u}}
    (K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ)
    (p : ℕ) (V : Y.Opens) :
    let E := PresheafOfModules.toPresheaf.{u} Y.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
    let P := (K.sc p).map (SheafOfModules.forget.{u} Y.ringCatSheaf)
    let k := (P.isoCyclesOfIsLimit (KernelFork.mapIsLimit _ (K.sc p).cyclesIsKernel
      (SheafOfModules.forget.{u} Y.ringCatSheaf))).inv
    (P.map E).homologyπ ≫ (P.mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) =
      (P.mapCyclesIso E).hom ≫ E.map k ≫ Hom.app (K.sc p).homologyπ V := by
  dsimp only
  rw [← Category.assoc, homologyπ_mapHomologyIso_hom, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  have h := adjoint_homology_comparison_cycles
    (PresheafOfModules.sheafification.{u} (𝟙 Y.ringCatSheaf.obj))
    (SheafOfModules.forget.{u} Y.ringCatSheaf)
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)) (K.sc p)
  dsimp only at h
  change _ ≫ (PresheafOfModules.toPresheaf.{u} Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)).map
      (((K.sc p).map (SheafOfModules.forget.{u} Y.ringCatSheaf)).homologyπ ≫
        sectionCohomologyTheta K p) = _
  rw [show ((K.sc p).map (SheafOfModules.forget.{u} Y.ringCatSheaf)).homologyπ ≫
      sectionCohomologyTheta K p = _ from h, CategoryTheory.Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules
