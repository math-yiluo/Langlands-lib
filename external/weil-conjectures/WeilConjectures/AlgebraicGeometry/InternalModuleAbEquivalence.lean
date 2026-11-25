/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.Monoidal.Mod

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Internal modules in abelian groups and ordinary modules

Source: the tensor-product universal property for bilinear module actions,
used sectionwise in Bhatt--Scholze, Section 5.3
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj TensorProduct

namespace CategoryTheory

variable (R : Type u) [Ring R] (M : Mod Ab.{u} (AddCommGrpCat.of R))

private noncomputable instance internalModule : Module R M.X where
  smul a m := (γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)
  one_smul m := by
    have h := congrArg (fun f ↦ f.hom (ULift.up (1 : ℤ) ⊗ₜ[ℤ] m))
      (ModObj.one_smul_self (AddCommGrpCat.of R) M.X)
    simp only [AddCommGrpCat.comp_apply,
      AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
      AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul, one_zsmul] at h
    have hη : (η[AddCommGrpCat.of R]).hom (ULift.up (1 : ℤ)) = (1 : R) := by
      simpa using AddCommGrpCat.ringMonObj_one_apply R (ULift.up (1 : ℤ))
    rw [hη] at h
    exact h
  mul_smul a b m := by
    have h := congrArg (fun f ↦ f.hom ((a ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] m))
      (ModObj.mul_smul (M := AddCommGrpCat.of R) M.X)
    exact h
  smul_zero a := by
    change (γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] (0 : M.X)) = 0
    simp
  smul_add a m n := by
    change (γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] (m + n)) = _
    simp only [TensorProduct.tmul_add, map_add]
    rfl
  zero_smul m := by
    change (γ[AddCommGrpCat.of R,M.X]).hom ((0 : R) ⊗ₜ[ℤ] m) = 0
    simp
  add_smul a b m := by
    change (γ[AddCommGrpCat.of R,M.X]).hom ((a + b) ⊗ₜ[ℤ] m) = _
    simp only [TensorProduct.add_tmul, map_add]
    rfl

private noncomputable def internalToModule : Mod Ab.{u} (AddCommGrpCat.of R) ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R M.X
  map {M N} f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := map_add f.hom.hom
      map_smul' := fun a m ↦ by
        have h := congrArg (fun g ↦ g.hom (a ⊗ₜ[ℤ] m))
          (IsModHom.smul_hom (A := AddCommGrpCat.of R) (f := f.hom))
        change f.hom.hom ((γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)) =
          (γ[AddCommGrpCat.of R,N.X]).hom (a ⊗ₜ[ℤ] f.hom.hom m)
        change f.hom.hom ((γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)) =
          (γ[AddCommGrpCat.of R,N.X]).hom (a ⊗ₜ[ℤ] f.hom.hom m) at h
        exact h }
  map_id M := rfl
  map_comp f g := rfl

private noncomputable def ordinaryAct (N : ModuleCat.{u} R) :
    AddCommGrpCat.of R ⊗ AddCommGrpCat.of N ⟶ AddCommGrpCat.of N :=
  AddCommGrpCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : R) (m : N) ↦ a • m)
    (fun a b m ↦ add_smul a b m)
    (fun c a m ↦ smul_assoc c a m)
    (fun a m n ↦ smul_add a m n)
    (fun c a m ↦ smul_comm a c m))).toAddMonoidHom

private noncomputable def moduleToInternalObj (N : ModuleCat.{u} R) :
    Mod Ab.{u} (AddCommGrpCat.of R) := by
  letI : ModObj (AddCommGrpCat.of R) (AddCommGrpCat.of N) :=
    ModObj.mk' (AddCommGrpCat.of R) (ordinaryAct R N)
      (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun n m ↦ by
        change (n.down : R) • m = n.down • m
        exact Int.cast_smul_eq_zsmul R n.down m))
      (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun a b m ↦ by
        exact mul_smul a b m))
  exact ⟨AddCommGrpCat.of N⟩

private noncomputable def moduleToInternalHom {M N : Mod Ab.{u} (AddCommGrpCat.of R)}
    (f : (internalToModule R).obj M ⟶ (internalToModule R).obj N) : M ⟶ N :=
  Mod.homMk (AddCommGrpCat.ofHom f.hom.toAddMonoidHom)
    (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a m ↦ by
      exact f.hom.map_smul a m))

private noncomputable def internalToModuleFullyFaithful : (internalToModule R).FullyFaithful where
  preimage f := moduleToInternalHom R f
  map_preimage f := by ext m; rfl
  preimage_map f := Mod.hom_ext _ _ rfl

private instance : (internalToModule R).Full := (internalToModuleFullyFaithful R).full
private instance : (internalToModule R).Faithful := (internalToModuleFullyFaithful R).faithful

private noncomputable def realizationIso (N : ModuleCat.{u} R) :
    (internalToModule R).obj (moduleToInternalObj R N) ≅ N :=
  ModuleCat.isoMk (Iso.refl _) (fun _ ↦ rfl)

private instance : (internalToModule R).EssSurj where
  mem_essImage N := ⟨moduleToInternalObj R N, ⟨realizationIso R N⟩⟩

private instance : (internalToModule R).IsEquivalence where

/-- Internal modules over the ring object associated to R are ordinary R-modules,
with exactly the same underlying abelian groups and maps.

Source: the universal property of the tensor product over ℤ, applied to a module
scalar action; the pointwise encoding step used in Bhatt--Scholze, Section 5.3
(auxiliary; not a blueprint node).

Proof in words. An internal action γ : R ⊗ℤ M → M gives scalar multiplication by
r • m = γ(r ⊗ m). Evaluate the internal unit equation at 1 ⊗ m and its associativity
equation at (r ⊗ s) ⊗ m to obtain the module unit and associativity laws. The additive
laws follow from bilinearity. Evaluating an internal linearity diagram at r ⊗ m
makes its additive map R-linear. Conversely the bilinear scalar multiplication of an
ordinary module gives γ by the tensor universal property. Its unit and associativity
diagrams hold because they hold on pure tensors. Likewise any ordinary linear map
is internally linear, so the constructed functor is fully faithful. The inverse
construction on objects realizes each ordinary module, with the identity map on the
underlying group as the realization isomorphism. This proves essential surjectivity
and hence equivalence. The functor forgets to the original group and map by definition.
The zero ring and zero module are included, and no commutativity is required. -/
theorem internalModuleAb_equivalence :
    ∃ F : Mod Ab.{u} (AddCommGrpCat.of R) ⥤ ModuleCat.{u} R,
      F.IsEquivalence ∧
      F ⋙ forget₂ (ModuleCat.{u} R) Ab.{u} = Mod.forget (AddCommGrpCat.of R) := by
  exact ⟨internalToModule R, inferInstance, rfl⟩

end CategoryTheory
