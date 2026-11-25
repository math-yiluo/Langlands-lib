/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.TwistedActionRingedSiteData
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-! # Explicit tensor comparisons for restriction of module sheaves

The comparison is constructed by transposing the restricted sheafification unit.
For a continuous cocontinuous functor and an isomorphism of coefficient rings,
it is invertible and carries sheafified pure tensors to pure tensors.
Source: Stacks 03CY and 03EK; the module-sheafification adjunction.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite.TensorRestriction

section SheafificationComparison

universe c v r c₂ v₂

end SheafificationComparison

theorem tensorIso_braiding {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}} (M N : Modules R) :
    (β_ M N).hom ≫ (SheafOfModules.tensorObjIsoSheafification N M).hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ring R).obj)).map (β_ M.val N.val).hom := by
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    MonoidalCategory.tensorIso_inv, Functor.Monoidal.μIso_hom, Category.assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  erw [Functor.LaxBraided.braided]
  rfl

theorem pure_braiding {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (M N : Modules R) (X : Cᵒᵖ) (x : M.val.obj X) (y : N.val.obj X) :
    (β_ M N).hom.val.app X (pureTensor M N X x y) = pureTensor N M X y x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ring R).obj)
  have h : (SheafOfModules.tensorObjIsoSheafification M N).inv ≫ (β_ M N).hom =
      (PresheafOfModules.sheafification (𝟙 (ring R).obj)).map (β_ M.val N.val).hom ≫
        (SheafOfModules.tensorObjIsoSheafification N M).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_braiding,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun k ↦ k.app X (x ⊗ₜ[R.obj.obj X] y))
    (adj.unit.naturality (β_ M.val N.val).hom)
  have hb : (β_ M.val N.val).hom.app X (x ⊗ₜ[R.obj.obj X] y) =
      y ⊗ₜ[R.obj.obj X] x := by
    erw [PresheafOfModules.braiding_hom_app (R := R.obj) M.val N.val X]
    exact ModuleCat.MonoidalCategory.braiding_hom_apply
      (R := R.obj.obj X) (M := M.val.obj X) (N := N.val.obj X) x y
  change ((adj.unit.app (N.val ⊗ M.val)).app X
    ((β_ M.val N.val).hom.app X (x ⊗ₜ[R.obj.obj X] y))) = _ at hh
  rw [hb] at hh
  have he := congrArg (fun k ↦ k.val.app X
    ((adj.unit.app (M.val ⊗ N.val)).app X (x ⊗ₜ[R.obj.obj X] y))) h
  exact he.trans
    (congrArg ((SheafOfModules.tensorObjIsoSheafification N M).inv.val.app X) hh.symm)

section RestrictionTensor

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
    (c : (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R ≅ S)

end RestrictionTensor

end CategoryTheory.TwistedActionRingedSite.TensorRestriction
