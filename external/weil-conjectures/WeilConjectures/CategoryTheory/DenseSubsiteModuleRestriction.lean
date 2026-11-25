/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Modules under restriction to a dense subsite

Source: Bhatt--Scholze, Example 4.2.11, transport of coefficient structures.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u₁ v₁ u₂ v₂ w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [F.IsContinuous J K]
  [(F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).IsEquivalence]
  [(F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).IsEquivalence]
  (R : Sheaf K RingCat.{max u₁ v₁ u₂ v₂ w})
private noncomputable def moduleLift (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R)) :=
  (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).inv.obj ((toSheaf _).obj M)
private noncomputable def moduleLiftIso (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R)) :
    (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).obj (moduleLift J K F R M) ≅
      (toSheaf _).obj M :=
  (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).asEquivalence.counitIso.app _
private noncomputable def restrictedAction (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R)) :
    (F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).obj (
      (sheafCompose K (CategoryTheory.forget RingCat.{max u₁ v₁ u₂ v₂ w})).obj R ⊗
      (sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w})).obj (moduleLift J K F R M)) ⟶
      (F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).obj
        ((sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w})).obj
          (moduleLift J K F R M)) := by
  let e := moduleLiftIso J K F R M
  refine ⟨{ app := fun U ↦ ↾fun x ↦ e.inv.hom.app U
              ((show R.obj.obj (F.op.obj U) from x.1) •
                (show M.val.obj U from e.hom.hom.app U x.2))
            naturality := ?_ }⟩
  intro U V f
  ext x
  symm
  change (moduleLift J K F R M).obj.map (F.op.map f)
      (e.inv.hom.app U ((show R.obj.obj (F.op.obj U) from x.1) •
        (show M.val.obj U from e.hom.hom.app U x.2))) =
    e.inv.hom.app V (R.obj.map (F.op.map f) x.1 •
      (show M.val.obj V from
      e.hom.hom.app V ((moduleLift J K F R M).obj.map (F.op.map f) x.2)))
  have hi := congrArg (fun t ↦ t
    ((show R.obj.obj (F.op.obj U) from x.1) •
      (show M.val.obj U from e.hom.hom.app U x.2))) (e.inv.hom.naturality f)
  have hh := congrArg (fun t ↦ t x.2) (e.hom.hom.naturality f)
  change _ = (moduleLift J K F R M).obj.map (F.op.map f)
    (e.inv.hom.app U ((show R.obj.obj (F.op.obj U) from x.1) •
      (show M.val.obj U from e.hom.hom.app U x.2))) at hi
  rw [← hi]
  change e.hom.hom.app V ((moduleLift J K F R M).obj.map (F.op.map f) x.2) =
    M.val.map f (e.hom.hom.app U x.2) at hh
  exact congrArg (fun m : M.val.obj V ↦ e.inv.hom.app V m)
    ((M.val.map_smul f x.1 (e.hom.hom.app U x.2)).trans
      (congrArg (fun m : M.val.obj V ↦ R.obj.map (F.op.map f) x.1 • m) hh.symm))
private noncomputable def liftAction (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R)) :=
  (F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).preimage
    (restrictedAction J K F R M)

private noncomputable def liftSmul (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))
    (U : Dᵒᵖ) (r : R.obj.obj U) (m : (moduleLift J K F R M).obj.obj U) :
    (moduleLift J K F R M).obj.obj U :=
  (liftAction J K F R M).hom.app U (r, m)

private theorem liftSmul_naturality (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))
    {U V : Dᵒᵖ} (f : U ⟶ V) (r : R.obj.obj U)
    (m : (moduleLift J K F R M).obj.obj U) :
    (moduleLift J K F R M).obj.map f (liftSmul J K F R M U r m) =
      liftSmul J K F R M V (R.obj.map f r) ((moduleLift J K F R M).obj.map f m) := by
  exact (congrArg (fun t ↦ t (r, m)) ((liftAction J K F R M).hom.naturality f)).symm

private theorem liftSmul_apply (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))
    (U : Cᵒᵖ) (r : R.obj.obj (F.op.obj U))
    (m : (moduleLift J K F R M).obj.obj (F.op.obj U)) :
    (moduleLiftIso J K F R M).hom.hom.app U (liftSmul J K F R M (F.op.obj U) r m) =
      r • (show M.val.obj U from (moduleLiftIso J K F R M).hom.hom.app U m) := by
  have h := congrArg (fun t ↦ t.hom.app U (r, m))
    ((F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).map_preimage
      (restrictedAction J K F R M))
  change liftSmul J K F R M (F.op.obj U) r m = _ at h
  rw [h]
  dsimp only [restrictedAction]
  exact congrArg (fun t ↦ t.hom.app U
    (r • (show M.val.obj U from (moduleLiftIso J K F R M).hom.hom.app U m)))
      (moduleLiftIso J K F R M).inv_hom_id
variable [F.IsCoverDense K]

omit [(F.sheafPushforwardContinuous (Type (max u₁ v₁ u₂ v₂ w)) J K).IsEquivalence] in
private theorem lift_ext (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))
    (U : Dᵒᵖ) (x y : (moduleLift J K F R M).obj.obj U)
    (h : ∀ (V : C) (f : F.obj V ⟶ U.unop),
      (moduleLiftIso J K F R M).hom.hom.app (op V)
        ((moduleLift J K F R M).obj.map f.op x) =
      (moduleLiftIso J K F R M).hom.hom.app (op V)
        ((moduleLift J K F R M).obj.map f.op y)) : x = y := by
  apply Functor.IsCoverDense.ext F
    ((sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w})).obj
      (moduleLift J K F R M)) U.unop
  intro V f
  exact (ConcreteCategory.bijective_of_isIso
    ((moduleLiftIso J K F R M).hom.hom.app (op V))).1 (h V f)

@[instance_reducible]
private noncomputable def liftModule (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))
    (U : Dᵒᵖ) : Module (R.obj.obj U) ((moduleLift J K F R M).obj.obj U) where
  smul := liftSmul J K F R M U
  one_smul m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_one, one_smul]
  mul_smul r s m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply, liftSmul_naturality,
      liftSmul_apply, liftSmul_naturality, liftSmul_apply]
    simp only [map_mul, mul_smul]
  smul_zero r := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_zero, smul_zero]
  smul_add r m n := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_add, smul_add]
    erw [liftSmul_naturality, liftSmul_apply, liftSmul_naturality, liftSmul_apply]
  add_smul r s m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_add, add_smul]
    erw [liftSmul_naturality, liftSmul_apply, liftSmul_naturality, liftSmul_apply]
  zero_smul m := by
    apply lift_ext J K F R M U
    intro V f
    erw [liftSmul_naturality, liftSmul_apply]
    simp only [map_zero, zero_smul]
private noncomputable def liftedModule (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R)) :
    SheafOfModules.{max u₁ v₁ u₂ v₂ w} R := by
  let (U : Dᵒᵖ) := liftModule J K F R M U
  exact ⟨PresheafOfModules.ofPresheaf (moduleLift J K F R M).obj
    (fun {_ _} f r m ↦ liftSmul_naturality J K F R M f r m),
      (moduleLift J K F R M).property⟩

private noncomputable def liftedModuleIso (M : SheafOfModules.{max u₁ v₁ u₂ v₂ w}
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R)) :
    (pushforward.{max u₁ v₁ u₂ v₂ w} (F := F) (J := J) (𝟙
      ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))).obj
        (liftedModule J K F R M) ≅ M := by
  let α : (pushforward.{max u₁ v₁ u₂ v₂ w} (F := F) (J := J) (𝟙
      ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))).obj
        (liftedModule J K F R M) ⟶ M :=
    ⟨PresheafOfModules.homMk (moduleLiftIso J K F R M).hom.hom
      (fun U r m ↦ liftSmul_apply J K F R M U r m)⟩
  have : IsIso ((toSheaf _).map α) := by
    change IsIso (moduleLiftIso J K F R M).hom
    infer_instance
  have : IsIso α := isIso_of_reflects_iso α (toSheaf _)
  exact asIso α
/-- Dense restriction equivalences on sets and abelian groups lift to arbitrary
ring-sheaf modules.

Source: Bhatt--Scholze, Example 4.2.11, transport of coefficient structures
(auxiliary; not a blueprint node).

Proof: Lift the underlying abelian sheaf through the restriction equivalence.
Conjugate the scalar action by its counit isomorphism on the smaller site and lift
this map of set sheaves using fullness of restriction. Check each module law on
covering test objects, where it is the original module law. Naturality gives a
presheaf of modules and its abelian sheaf property gives a sheaf of modules.
The counit isomorphism is linear, proving essential surjectivity. A map lifts by
fullness on abelian sheaves; test scalar compatibility on the dense subsite to
prove it is linear. Faithfulness follows from faithfulness on abelian sheaves. -/
theorem isEquivalence_pushforward_of_dense :
    (pushforward.{max u₁ v₁ u₂ v₂ w} (F := F) (J := J) (𝟙
      ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))).IsEquivalence := by
  let P := pushforward.{max u₁ v₁ u₂ v₂ w} (F := F) (J := J) (𝟙
    ((F.sheafPushforwardContinuous RingCat.{max u₁ v₁ u₂ v₂ w} J K).obj R))
  have : P.Faithful := by
    constructor
    intro M N f g h
    apply (toSheaf R).map_injective
    apply (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).map_injective
    exact congrArg ((toSheaf _).map) h
  have : P.Full := by
    constructor
    intro M N f
    let α := (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).preimage
      (X := (toSheaf R).obj M) (Y := (toSheaf R).obj N) ((toSheaf _).map f)
    have hα := (F.sheafPushforwardContinuous Ab.{max u₁ v₁ u₂ v₂ w} J K).map_preimage
      (X := (toSheaf R).obj M) (Y := (toSheaf R).obj N) ((toSheaf _).map f)
    have happ (V : Cᵒᵖ) (m : M.val.obj (F.op.obj V)) :
        α.hom.app (F.op.obj V) m = f.val.app V m := by
      exact congrArg (fun t ↦ t.hom.app V m) hα
    have hlin (U : Dᵒᵖ) (r : R.obj.obj U) (m : M.val.obj U) :
        α.hom.app U (r • m) = r • (show N.val.obj U from α.hom.app U m) := by
      apply Functor.IsCoverDense.ext F
        ((sheafCompose K (CategoryTheory.forget Ab.{max u₁ v₁ u₂ v₂ w})).obj
          ((toSheaf R).obj N)) U.unop
      intro V g
      have hn (x : M.val.obj U) :
          N.val.map g.op (α.hom.app U x) =
            α.hom.app (op (F.obj V)) (M.val.map g.op x) :=
        (congrArg (fun t ↦ t x) (α.hom.naturality g.op)).symm
      change N.val.map g.op (α.hom.app U (r • m)) =
        N.val.map g.op (r • (show N.val.obj U from α.hom.app U m))
      rw [hn, M.val.map_smul, N.val.map_smul, hn]
      erw [happ (op V), happ (op V)]
      exact (f.val.app (op V)).hom.map_smul _ _
    refine ⟨⟨PresheafOfModules.homMk α.hom hlin⟩, ?_⟩
    apply (toSheaf _).map_injective
    exact hα
  have : P.EssSurj := ⟨fun M ↦ ⟨liftedModule J K F R M, ⟨liftedModuleIso J K F R M⟩⟩⟩
  change P.IsEquivalence
  exact {}
end SheafOfModules
