/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! Pointwise composition formula for structure-sheaf cohomology pullback.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise)
-/

@[expose] public section

universe u

open CategoryTheory

private theorem adjoint_comp_mate {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ Rf ⋙ Rg)
    {A : C} {B : D} {T : E} (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k) =
      (adj.leftAdjointUniq (adjg.comp adjf)).hom.app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k)
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _)
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]

private theorem adjoint_constant_comp {A C D E : Type*}
    [Category A] [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ Rf ⋙ Rg)
    {PZ : A ⥤ C} {SZ : C ⥤ A} {PY : A ⥤ D} {PX : A ⥤ E}
    (cz : PZ ⊣ SZ) (cy : PY ⊣ Rg ⋙ SZ) (cx : PX ⊣ Rf ⋙ Rg ⋙ SZ) (a : A)
    (eg : Lg.obj (PZ.obj a) ⟶ PY.obj a)
    (ef : Lf.obj (PY.obj a) ⟶ PX.obj a) (efg : L.obj (PZ.obj a) ⟶ PX.obj a)
    (hg : (cz.comp adjg).homEquiv a (PY.obj a) eg = cy.unit.app a)
    (hf : (cy.comp adjf).homEquiv a (PX.obj a) ef = cx.unit.app a)
    (hfg : (cz.comp adj).homEquiv a (PX.obj a) efg = cx.unit.app a) :
    efg = (adj.leftAdjointUniq (adjg.comp adjf)).hom.app (PZ.obj a) ≫
      Lf.map eg ≫ ef := by
  apply ((cz.comp adj).homEquiv a (PX.obj a)).injective
  rw [hfg, Adjunction.comp_homEquiv]
  change _ = (cz.homEquiv _ _) ((adj.homEquiv _ _) _)
  rw [adj.homEquiv_naturality_right]
  dsimp only [Functor.id_obj]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app adj (adjg.comp adjf) (PZ.obj a)]
  change _ = (cz.homEquiv _ _) (((adjg.comp adjf).homEquiv _ _) _)
  rw [Adjunction.comp_homEquiv]
  change _ = (cz.homEquiv _ _) ((adjg.homEquiv _ _) ((adjf.homEquiv _ _) _))
  rw [adjf.homEquiv_naturality_left, adjg.homEquiv_naturality_right,
    cz.homEquiv_naturality_right]
  rw [Adjunction.comp_homEquiv] at hg hf
  change (cz.homEquiv _ _) ((adjg.homEquiv _ _) _) = cy.unit.app a at hg
  change (cy.homEquiv _ _) ((adjf.homEquiv _ _) _) = cx.unit.app a at hf
  rw [hg]
  exact hf.symm

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4000 in
/-- Pointwise form of the composition formula. The Ext construction of pullback
is functorial under composition of exact inverse-image functors; evaluating that
functoriality on a class gives the displayed equality. This is the pointwise
calculation underlying the additive-homomorphism composition law.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7, equation-functorial.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise)
-/
theorem structureSheafCohomologyPullback_comp_apply {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (x : Sheaf.H (structureSheafAb Z) n) :
    structureSheafCohomologyPullback (f ≫ g) n x =
      structureSheafCohomologyPullback f n
        (structureSheafCohomologyPullback g n x) := by
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  let JZ := Opens.grothendieckTopology Z
  have : HasSheafify JX AddCommGrpCat.{u} := inferInstance
  have : HasSheafify JY AddCommGrpCat.{u} := inferInstance
  have : HasSheafify JZ AddCommGrpCat.{u} := inferInstance
  let instX : Abelian (Sheaf JX AddCommGrpCat.{u}) := inferInstance
  let instY : Abelian (Sheaf JY AddCommGrpCat.{u}) := inferInstance
  let instZ : Abelian (Sheaf JZ AddCommGrpCat.{u}) := inferInstance
  have : HasExt.{u} (Sheaf JX AddCommGrpCat.{u}) := inferInstance
  have : HasExt.{u} (Sheaf JY AddCommGrpCat.{u}) := inferInstance
  have : HasExt.{u} (Sheaf JZ AddCommGrpCat.{u}) := inferInstance
  let F := TopologicalSpace.Opens.map f.base
  let G := TopologicalSpace.Opens.map g.base
  let FG := TopologicalSpace.Opens.map (f ≫ g).base
  let Lf := F.sheafPullback AddCommGrpCat.{u} JY JX
  let Lg := G.sheafPullback AddCommGrpCat.{u} JZ JY
  let Lfg := FG.sheafPullback AddCommGrpCat.{u} JZ JX
  let Rf := F.sheafPushforwardContinuous AddCommGrpCat.{u} JY JX
  let Rg := G.sheafPushforwardContinuous AddCommGrpCat.{u} JZ JY
  let Rfg := FG.sheafPushforwardContinuous AddCommGrpCat.{u} JZ JX
  let adjf : Lf ⊣ Rf := F.sheafAdjunctionContinuous AddCommGrpCat.{u} JY JX
  let adjg : Lg ⊣ Rg := G.sheafAdjunctionContinuous AddCommGrpCat.{u} JZ JY
  let adjfg : Lfg ⊣ Rfg := FG.sheafAdjunctionContinuous AddCommGrpCat.{u} JZ JX
  let adjcomp : Lg ⋙ Lf ⊣ Rf ⋙ Rg := adjg.comp adjf
  let α : Lfg ≅ Lg ⋙ Lf := adjfg.leftAdjointUniq adjcomp
  let OX := structureSheafAb X
  let OY := structureSheafAb Y
  let OZ := structureSheafAb Z
  let af : Lf.obj OY ⟶ OX := (adjf.homEquiv OY OX).symm
    (⟨Functor.whiskerRight f.c
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)
  let ag : Lg.obj OZ ⟶ OY := (adjg.homEquiv OZ OY).symm
    (⟨Functor.whiskerRight g.c
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)
  let afg : Lfg.obj OZ ⟶ OX := (adjfg.homEquiv OZ OX).symm
    (⟨Functor.whiskerRight (f ≫ g).c
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)
  have hstructure : afg = α.hom.app OZ ≫ Lf.map ag ≫ af := by
    exact adjoint_comp_mate adjg adjf adjfg (A := OZ) (B := OY) (T := OX)
      (⟨Functor.whiskerRight g.c
        (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)
      (⟨Functor.whiskerRight f.c
        (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u})⟩)
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let ZX := (constantSheaf JX AddCommGrpCat.{u}).obj A
  let ZY := (constantSheaf JY AddCommGrpCat.{u}).obj A
  let ZZ := (constantSheaf JZ AddCommGrpCat.{u}).obj A
  let ef : constantSheaf JY AddCommGrpCat.{u} ⋙ Lf ≅
      constantSheaf JX AddCommGrpCat.{u} := F.constantSheafsheafPullbackIso AddCommGrpCat.{u} JY JX
    Limits.isTerminalTop Limits.isTerminalTop
  let eg : constantSheaf JZ AddCommGrpCat.{u} ⋙ Lg ≅
      constantSheaf JY AddCommGrpCat.{u} := G.constantSheafsheafPullbackIso AddCommGrpCat.{u} JZ JY
    Limits.isTerminalTop Limits.isTerminalTop
  let efg : constantSheaf JZ AddCommGrpCat.{u} ⋙ Lfg ≅
      constantSheaf JX AddCommGrpCat.{u} := FG.constantSheafsheafPullbackIso AddCommGrpCat.{u} JZ JX
    Limits.isTerminalTop Limits.isTerminalTop
  let cz := constantSheafAdj JZ AddCommGrpCat.{u} Limits.isTerminalTop
  let cy := constantSheafAdj JY AddCommGrpCat.{u} Limits.isTerminalTop
  let cx := constantSheafAdj JX AddCommGrpCat.{u} Limits.isTerminalTop
  have hg : (cz.comp adjg).homEquiv A ZY (eg.hom.app A) = cy.unit.app A := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((cz.comp adjg).ofNatIsoRight
        (G.sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u} JZ JY
          (Opposite.op (⊤ : TopologicalSpace.Opens Z)))) cy A
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    change (cz.comp adjg).homEquiv A ZY (eg.hom.app A) ≫ 𝟙 _ = cy.unit.app A at h
    simpa only [Category.comp_id] using h
  have hf : (cy.comp adjf).homEquiv A ZX (ef.hom.app A) = cx.unit.app A := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((cy.comp adjf).ofNatIsoRight
        (F.sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u} JY JX
          (Opposite.op (⊤ : TopologicalSpace.Opens Y)))) cx A
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    change (cy.comp adjf).homEquiv A ZX (ef.hom.app A) ≫ 𝟙 _ = cx.unit.app A at h
    simpa only [Category.comp_id] using h
  have hfg : (cz.comp adjfg).homEquiv A ZX (efg.hom.app A) = cx.unit.app A := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((cz.comp adjfg).ofNatIsoRight
        (FG.sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u} JZ JX
          (Opposite.op (⊤ : TopologicalSpace.Opens Z)))) cx A
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    change (cz.comp adjfg).homEquiv A ZX (efg.hom.app A) ≫ 𝟙 _ = cx.unit.app A at h
    simpa only [Category.comp_id] using h
  have hc : efg.hom.app A = α.hom.app ZZ ≫ Lf.map (eg.hom.app A) ≫ ef.hom.app A :=
    adjoint_constant_comp adjg adjf adjfg cz cy cx A
      (eg.hom.app A) (ef.hom.app A) (efg.hom.app A) hg hf hfg
  have hconstant : efg.inv.app A ≫ α.hom.app ZZ =
      ef.inv.app A ≫ Lf.map (eg.inv.app A) := by
    have h := congrArg
      (fun t => efg.inv.app A ≫ t ≫ ef.inv.app A ≫ Lf.map (eg.inv.app A)) hc
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, ← Lf.map_comp, Iso.hom_inv_id_app] at h
    change ef.inv.app A ≫ Lf.map (eg.inv.app A) =
      efg.inv.app A ≫ α.hom.app ZZ ≫ Lf.map (𝟙 (Lg.obj ZZ)) at h
    dsimp only [Functor.comp_obj] at h ⊢
    simpa only [Lf.map_id, Category.comp_id] using h.symm
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) F
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) G
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) FG
  have : Limits.PreservesFiniteLimits Lf :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  have : Limits.PreservesFiniteLimits Lg :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  have : Limits.PreservesFiniteLimits Lfg :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  have : Limits.PreservesColimits Lf := adjf.leftAdjoint_preservesColimits
  have : Limits.PreservesColimits Lg := adjg.leftAdjoint_preservesColimits
  have : Limits.PreservesColimits Lfg := adjfg.leftAdjoint_preservesColimits
  have : Limits.PreservesBinaryBiproducts Lf :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryProducts Lf
  have : Limits.PreservesBinaryBiproducts Lg :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryProducts Lg
  have : Limits.PreservesBinaryBiproducts Lfg :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryProducts Lfg
  have : Lf.Additive := Functor.additive_of_preservesBinaryBiproducts Lf
  have : Lg.Additive := Functor.additive_of_preservesBinaryBiproducts Lg
  have : Lfg.Additive := Functor.additive_of_preservesBinaryBiproducts Lfg
  change ((Abelian.Ext.mk₀ (efg.inv.app A)).comp
    (x.mapExactFunctor Lfg) (zero_add n)).comp (Abelian.Ext.mk₀ afg) (add_zero n) =
    ((Abelian.Ext.mk₀ (ef.inv.app A)).comp
      (((Abelian.Ext.mk₀ (eg.inv.app A)).comp
        (x.mapExactFunctor Lg) (zero_add n)).comp (Abelian.Ext.mk₀ ag)
          (add_zero n) |>.mapExactFunctor Lf) (zero_add n)).comp
            (Abelian.Ext.mk₀ af) (add_zero n)
  rw [hstructure]
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_comp_mk₀]
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero
    (x.mapExactFunctor Lfg) (Abelian.Ext.mk₀ (α.hom.app OZ))]
  rw [Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf Lg Lf Lfg α x]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, hconstant, Abelian.Ext.mk₀_comp_mk₀_assoc]

end AlgebraicGeometry.Scheme
