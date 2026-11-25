/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Abelian.DerivedSingleShiftNormalization
import WeilConjectures.CategoryTheory.Abelian.DerivedBottomInclusion
import WeilConjectures.CategoryTheory.Abelian.DerivedCyclesUnitNaturality

/-! # Canonical-cycle transport to the double truncation

Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-cycle-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

/-- The part of the bottom comparison before the single-object normalization.
All maps are taken from its explicit double-truncation construction.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-cycle-transport). -/
noncomputable def rightDerivedBottomToSingleIso (n : ℤ) :
    DerivedCategory.TStructure.t.truncGE n ⋙ S.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D n ≅
    DerivedCategory.TStructure.t.truncGE n ⋙ DerivedCategory.homologyFunctor C n ⋙
      DerivedCategory.Plus.singleFunctor C n ⋙ S.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D n := by
  let t := DerivedCategory.TStructure.t (C := C)
  let tp := DerivedCategory.Plus.TStructure.t (C := C)
  let L := t.plus.lift (t.truncGE n) (fun K ↦ ⟨n, inferInstance⟩)
  let H := DerivedCategory.Plus.homologyFunctor D n
  let R := S.rightDerivedFunctorPlus
  let α := Functor.whiskerLeft L
    (Functor.whiskerRight (Functor.whiskerRight (tp.truncLTι (n + 1)) R) H)
  have (K : DerivedCategory C) : IsIso (α.app K) := by
    let M := L.obj K
    let T := (R ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      ((tp.triangleLTGE (n + 1)).obj M)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      (R ⋙ DerivedCategory.Plus.ι).map_distinguished _
        (tp.triangleLTGE_distinguished (n + 1) M)
    have hz (j : ℤ) (hj : j < n + 1) :
        Limits.IsZero ((DerivedCategory.homologyFunctor D j).obj T.obj₃) := by
      exact S.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((tp.truncGE (n + 1)).obj M) (n + 1) hj
    exact DerivedCategory.isIso_homologyMap_mor₁ T hT (n - 1) n (by omega)
      (hz (n - 1) (by omega)) (hz n (by omega))
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let β := Functor.whiskerLeft L
    (Functor.whiskerLeft (tp.truncLT (n + 1))
      (Functor.whiskerRight (Functor.whiskerRight (tp.truncGEπ n) R) H))
  have (K : DerivedCategory C) : IsIso (β.app K) := by
    have : tp.IsGE (L.obj K) n := by
      apply (DerivedCategory.Plus.isGE_ι_obj_iff (L.obj K) n).mp
      change t.IsGE ((t.truncGE n).obj K) n
      infer_instance
    have : IsIso ((tp.truncGEπ n).app ((tp.truncLT (n + 1)).obj (L.obj K))) :=
      inferInstance
    change IsIso (H.map (R.map _))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let eT := DerivedCategory.Plus.eTruncLTCompETruncGEIso (C := C) n
  let Hn := DerivedCategory.Plus.homologyFunctor C n
  let e := (asIso α).symm ≪≫ asIso β ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight eT (R ⋙ H))
  let HA := DerivedCategory.homologyFunctor D n
  let eP := Functor.isoWhiskerLeft L
    (Functor.isoWhiskerRight S.rightDerivedFunctorPlusCompatibility.symm HA)
  exact eP ≪≫ e

/-- Transport of canonical cycles to the actual unit on the single homology object.

Source: Stacks Project, Tag 05TC (2), with the unit of Tag 05TD (3).
(blueprint: new-lem-pc-derived-bottom-cycle-transport).

Proof: Lift the lower truncation to the bounded-below derived category and
map the single object of cycles into it using the canonical cycle inclusion.
The cycle-map homology formula identifies its homology coefficient with
the quotient followed by the lower-truncation homology map. Actual derived-unit
naturality, including bounded-below/unbounded compatibility, identifies the
original cycle prefix with the single unit followed by the derived cycle map.
Factor that map through the canonical bottom-homology inclusion. Naturality
of the single unit follows by cancelling its shifted comparison and applying
shift normalization. Move the homology coefficient across the unit, expand
the bottom inclusion, and cancel the upper inclusion, lower projection and
double-truncation identification against the explicit comparison. The upper
inclusion induces invertible derived bottom homology by the distinguished
triangle and vanishing below n + 1. The result stops at the actual single
unit; it does not compose the conclusion with the shifted comparison. -/
theorem rightDerivedBottom_cycle_transport (n : ℤ) (K : CochainComplex C ℤ) :
    ((((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).liftCycles
        (S.map (K.sc n).iCycles) (by
          change S.map (K.sc n).iCycles ≫ S.map (K.sc n).g = 0
          rw [← S.map_comp, (K.sc n).iCycles_g, S.map_zero])) ≫
      (((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).homologyπ ≫
          ((DerivedCategory.homologyFunctorFactors D n).app
            ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
          (DerivedCategory.homologyFunctor D n).map
            ((DerivedCategory.quotientCompQhIso D).inv.app
                ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
              S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
              S.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)) ≫
          (DerivedCategory.homologyFunctor D n).map
            (S.rightDerivedFunctor.map
              ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K))) ≫
          (S.rightDerivedBottomToSingleIso n).hom.app (DerivedCategory.Q.obj K) =
      S.map ((K.sc n).homologyπ ≫
        ((DerivedCategory.homologyFunctorFactors C n).app K).inv ≫
        (DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K))) ≫
      S.rightDerivedPlusSingleUnitHomologyAt n
        ((DerivedCategory.homologyFunctor C n).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj K))) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let tp := DerivedCategory.Plus.TStructure.t (C := C)
  let X := DerivedCategory.Q.obj K
  let L := t.plus.lift (t.truncGE n) (fun Z ↦ ⟨n, inferInstance⟩)
  let M := L.obj X
  let R := S.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor D n
  let HC := DerivedCategory.Plus.homologyFunctor C n
  let q : X ⟶ DerivedCategory.Plus.ι.obj M := (t.truncGEπ n).app X
  let Y := (K.sc n).cycles
  let f : (DerivedCategory.Plus.singleFunctor C n).obj Y ⟶ M :=
    DerivedCategory.Plus.ι.preimage (DerivedCategory.cyclesDerivedMap n K ≫ q)
  have hM : tp.IsGE M n := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff M n).mp
    change t.IsGE ((t.truncGE n).obj X) n
    infer_instance
  let a := (tp.truncLTι (n + 1)).app M
  let b := (tp.truncGEπ n).app ((tp.truncLT (n + 1)).obj M)
  let e := (DerivedCategory.Plus.eTruncLTCompETruncGEIso n).app M
  have : IsIso b := inferInstance
  have : IsIso (H.map (R.map a)) := by
    let T := (R ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      ((tp.triangleLTGE (n + 1)).obj M)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      (R ⋙ DerivedCategory.Plus.ι).map_distinguished _
        (tp.triangleLTGE_distinguished (n + 1) M)
    have hz (j : ℤ) (hj : j < n + 1) :
        IsZero ((DerivedCategory.homologyFunctor D j).obj T.obj₃) :=
      S.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((tp.truncGE (n + 1)).obj M) (n + 1) hj
    exact DerivedCategory.isIso_homologyMap_mor₁ T hT (n - 1) n (by omega)
      (hz (n - 1) (by omega)) (hz n (by omega))
  have hq : (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app Y ≫
      HC.map f = (K.sc n).homologyπ ≫
        (DerivedCategory.homologyFunctorFactors C n).inv.app K ≫
        (DerivedCategory.homologyFunctor C n).map q := by
    change (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app Y ≫
      (DerivedCategory.homologyFunctor C n).map (DerivedCategory.Plus.ι.map f) = _
    rw [Functor.map_preimage]
    simp only [Functor.map_comp]
    rw [reassoc_of% (DerivedCategory.cyclesDerivedMap_homology n K)]
  have hf : f = (DerivedCategory.Plus.singleFunctor C n).map
      ((K.sc n).homologyπ ≫ (DerivedCategory.homologyFunctorFactors C n).inv.app K ≫
        (DerivedCategory.homologyFunctor C n).map q) ≫
      DerivedCategory.Plus.bottomHomologyInclusion n M := by
    rw [DerivedCategory.Plus.single_map_bottomHomologyInclusion n M Y f, hq]
  have hu (Z : C) (g : Y ⟶ Z) :
      S.rightDerivedPlusSingleUnitHomologyAt n Y ≫
        H.map (R.map ((DerivedCategory.Plus.singleFunctor C n).map g)) =
      S.map g ≫ S.rightDerivedPlusSingleUnitHomologyAt n Z := by
    let c := S.rightDerivedPlusSingleShiftIso n
    apply (cancel_mono (c.hom.app Z)).mp
    simp only [Category.assoc]
    change S.rightDerivedPlusSingleUnitHomologyAt n Y ≫
      (DerivedCategory.Plus.singleFunctor C n ⋙ R ⋙ H).map g ≫ c.hom.app Z = _
    rw [c.hom.naturality]
    erw [reassoc_of% (S.rightDerivedPlusSingleUnitHomologyAt_comp_shiftIso n Y),
      S.rightDerivedPlusSingleUnitHomologyAt_comp_shiftIso n Z]
    simp only [Category.comp_id]
  simp only [rightDerivedBottomToSingleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    asIso_inv, asIso_hom, NatIso.isIso_inv_app, Functor.comp_map]
  erw [reassoc_of% (S.rightDerived_cycles_unit_naturality n K M q)]
  change S.rightDerivedPlusSingleUnitHomologyAt n Y ≫ H.map (R.map f) ≫
    CategoryTheory.inv (H.map (R.map a)) ≫ H.map (R.map b) ≫ H.map (R.map e.hom) = _
  rw [hf, R.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hu _ _)]
  dsimp only [DerivedCategory.Plus.bottomHomologyInclusion]
  change S.map _ ≫ S.rightDerivedPlusSingleUnitHomologyAt n (HC.obj M) ≫
    H.map (R.map (e.inv ≫ CategoryTheory.inv b ≫ a)) ≫ CategoryTheory.inv (H.map (R.map a)) ≫
      H.map (R.map b) ≫ H.map (R.map e.hom) = _
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc,
    IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  erw [H.map_id, Category.comp_id]
  rfl

end CategoryTheory.Functor
