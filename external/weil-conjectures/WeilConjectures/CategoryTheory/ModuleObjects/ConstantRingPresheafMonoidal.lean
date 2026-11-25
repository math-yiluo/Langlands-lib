/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# Presheaves of modules over a constant ring as module objects, compatibly with `⊗`

Let `T` be a commutative ring. The equivalence `CategoryTheory.Presheaf.moduleToMod` between
presheaves of `T`-modules and module objects over the constant ring presheaf `T` in abelian
presheaves is compatible with the tensor products: the objectwise tensor product `N₁ ⊗_T N₂` on
the one side, the relative tensor product of module objects (a coequalizer of
`N₁ ⊗ T ⊗ N₂ ⇉ N₁ ⊗ N₂`) on the other side.

Objectwise this is the statement that `A ⊗_ℤ B ⟶ A ⊗_T B` is the coequalizer of
`(t a) ⊗ b` and `a ⊗ (t b)`, for `T`-modules `A` and `B`. The comparison
`N₁ ⊗_T N₂ ⟶ toMod N₁ ⊗ toMod N₂` is built objectwise from the balanced map `a ⊗ b ↦ π (a ⊗ b)`
(`TensorProduct.liftAddHom`), its inverse from the universal property of the relative tensor
product.

## Main definitions

* `CategoryTheory.Presheaf.preservesColimitsOfSize_tensorLeft`: tensoring with an abelian
  presheaf preserves colimits, so that module objects over a commutative ring object of abelian
  presheaves have a relative tensor product.
* `CategoryTheory.Presheaf.toModTensorIso`: `toMod (N₁ ⊗ N₂) ≅ toMod N₁ ⊗ toMod N₂`.
* `CategoryTheory.Presheaf.moduleToModTensorIso`: the natural isomorphism of bifunctors
  expressing that `moduleToMod` commutes with `⊗`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Opposite Limits
open scoped CategoryTheory.Obj TensorProduct

namespace CategoryTheory.Presheaf

variable {C : Type (u + 1)} [Category.{u} C] (T : Type (u + 1)) [CommRing T]

open scoped MonoidalClosed.FunctorCategory in
/-- Tensoring on the left with an abelian presheaf preserves colimits (computed objectwise). -/
instance preservesColimitsOfSize_tensorLeft (X : Cᵒᵖ ⥤ Ab.{u + 1}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

open scoped MonoidalClosed.FunctorCategory in
/-- Tensoring on the right with an abelian presheaf preserves colimits (computed objectwise). -/
instance preservesColimitsOfSize_tensorRight (X : Cᵒᵖ ⥤ Ab.{u + 1}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) where
  preservesColimitsOfShape := ⟨inferInstance⟩

variable {T}

section TensorIso

variable (N₁ N₂ : Cᵒᵖ ⥤ ModuleCat.{u + 1} T)

/-- The projection onto the relative tensor product of module objects is balanced for the
action of `T` on sections. -/
lemma tensorObjπ_app_smul_tmul (U : Cᵒᵖ) (t : T) (a : N₁.obj U) (b : N₂.obj U) :
    ((Mod.tensorObjπ (toMod T N₁) (toMod T N₂)).app U).hom ((t • a) ⊗ₜ[ℤ] b) =
      ((Mod.tensorObjπ (toMod T N₁) (toMod T N₂)).app U).hom (a ⊗ₜ[ℤ] (t • b)) :=
  congrArg (fun f ↦ (f.app U).hom ((a ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] b))
    (Mod.tensorObjπ_condition (toMod T N₁) (toMod T N₂))

/-- The component at `U` of the comparison from the objectwise tensor product over `T` to the
relative tensor product of the associated module objects: `a ⊗ b ↦ π (a ⊗ b)`. -/
noncomputable def tensorToModTensorApp (U : Cᵒᵖ) :
    N₁.obj U ⊗[T] N₂.obj U →+ ((toMod T N₁ ⊗ toMod T N₂).X.obj U) :=
  TensorProduct.liftAddHom
    { toFun a :=
        { toFun b := ((Mod.tensorObjπ (toMod T N₁) (toMod T N₂)).app U).hom (a ⊗ₜ[ℤ] b)
          map_zero' := by simp
          map_add' b b' := by simp [TensorProduct.tmul_add] }
      map_zero' := by
        ext b
        simp
      map_add' a a' := by
        ext b
        simp [TensorProduct.add_tmul] }
    (tensorObjπ_app_smul_tmul N₁ N₂ U)

/-- `tensorToModTensorApp` on pure tensors. -/
@[simp]
lemma tensorToModTensorApp_tmul (U : Cᵒᵖ) (a : N₁.obj U) (b : N₂.obj U) :
    tensorToModTensorApp N₁ N₂ U (a ⊗ₜ[T] b) =
      ((Mod.tensorObjπ (toMod T N₁) (toMod T N₂)).app U).hom (a ⊗ₜ[ℤ] b) :=
  rfl

/-- The comparison from the objectwise tensor product of presheaves of `T`-modules to the relative
tensor product of the associated module objects, as a morphism of abelian presheaves. -/
noncomputable def tensorToModTensor :
    (toMod T (N₁ ⊗ N₂)).X ⟶ (toMod T N₁ ⊗ toMod T N₂).X where
  app U := AddCommGrpCat.ofHom (tensorToModTensorApp N₁ N₂ U)
  naturality U V f := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      exact congrArg (fun g ↦ g.hom (a ⊗ₜ[ℤ] b))
        ((Mod.tensorObjπ (toMod T N₁) (toMod T N₂)).naturality f)
    | add x y hx hy => simp_all

/-- The comparison `tensorToModTensor` is `T`-linear. -/
lemma tensorToModTensor_linear :
    γ[constRingObj (C := C) T, (toMod T (N₁ ⊗ N₂)).X] ≫ tensorToModTensor N₁ N₂ =
      constRingObj T ◁ tensorToModTensor N₁ N₂ ≫
        γ[constRingObj (C := C) T, (toMod T N₁ ⊗ toMod T N₂).X] := by
  refine NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
    (TensorProduct.ext' fun (t : T) x ↦ ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    exact (congrArg (fun g ↦ (g.app U).hom (t ⊗ₜ[ℤ] (a ⊗ₜ[ℤ] b)))
      (Mod.whiskerLeft_tensorπ_smul (toMod T N₁) (toMod T N₂))).symm
  | add x y hx hy => simp_all [TensorProduct.tmul_add]

/-- The projection `N₁ ⊗_ℤ N₂ ⟶ N₁ ⊗_T N₂` from the tensor product of the underlying abelian
presheaves to the objectwise tensor product over `T`. -/
noncomputable def moduleTensorπ :
    (toMod T N₁).X ⊗ (toMod T N₂).X ⟶ (toMod T (N₁ ⊗ N₂)).X where
  app U := AddCommGrpCat.ofHom
    (TensorProduct.mapOfCompatibleSMul T ℤ ℤ (N₁.obj U) (N₂.obj U)).toAddMonoidHom
  naturality _ _ _ := AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)

/-- The projection `moduleTensorπ` is balanced for the two actions of `T`. -/
lemma moduleTensorπ_balanced :
    ((β_ (toMod T N₁).X (constRingObj T)).hom ≫ γ[constRingObj (C := C) T, (toMod T N₁).X]) ▷
        (toMod T N₂).X ≫ moduleTensorπ N₁ N₂ =
      ((α_ (toMod T N₁).X (constRingObj T) (toMod T N₂).X).hom ≫
        (toMod T N₁).X ◁ γ[constRingObj (C := C) T, (toMod T N₂).X]) ≫ moduleTensorπ N₁ N₂ :=
  NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
    (TensorProduct.ext_threefold fun (a : N₁.obj U) (t : T) (b : N₂.obj U) ↦
      TensorProduct.smul_tmul t a b))

/-- The comparison from the relative tensor product of the module objects associated with `N₁` and
`N₂` to the objectwise tensor product over `T`, induced by `moduleTensorπ`. -/
noncomputable def modTensorToTensor :
    (toMod T N₁ ⊗ toMod T N₂).X ⟶ (toMod T (N₁ ⊗ N₂)).X :=
  Mod.tensorObjDesc _ _ (moduleTensorπ N₁ N₂) (moduleTensorπ_balanced N₁ N₂)

/-- The objectwise tensor product over `T` of presheaves of `T`-modules is the relative tensor
product of the associated module objects. -/
noncomputable def toModTensorIso :
    toMod T (N₁ ⊗ N₂) ≅ toMod T N₁ ⊗ toMod T N₂ :=
  Mod.isoMk
    { hom := tensorToModTensor N₁ N₂
      inv := modTensorToTensor N₁ N₂
      hom_inv_id := by
        refine NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
          (LinearMap.ext fun x ↦ ?_))
        induction x using TensorProduct.inductionOn with
        | tmul a b =>
          exact congrArg (fun g ↦ (g.app U).hom (a ⊗ₜ[ℤ] b))
            (Mod.tensorObjπ_tensorObjDesc _ _ (moduleTensorπ N₁ N₂) (moduleTensorπ_balanced N₁ N₂))
        | add x y hx hy => simp_all
      inv_hom_id := by
        rw [← cancel_epi (Mod.tensorObjπ _ _), modTensorToTensor,
          Mod.tensorObjπ_tensorObjDesc_assoc, Category.comp_id]
        exact NatTrans.ext (funext fun _ ↦ AddCommGrpCat.hom_ext_toIntLinearMap
          (TensorProduct.ext' fun _ _ ↦ rfl)) }
    (tensorToModTensor_linear N₁ N₂)
end TensorIso

variable (T) in
/-- The equivalence `moduleToMod` between presheaves of `T`-modules and module objects over the
constant ring presheaf `T` commutes with the tensor products (objectwise `⊗_T`, and the relative
tensor product `⊗_T` of module objects), naturally in both variables. -/
noncomputable def moduleToModTensorIso :
    (Functor.postcompose₂.obj (moduleToMod (C := C) T)).obj
        (curriedTensor (Cᵒᵖ ⥤ ModuleCat.{u + 1} T)) ≅
      (((Functor.whiskeringLeft₂ _).obj (moduleToMod (C := C) T)).obj
        (moduleToMod (C := C) T)).obj
        (curriedTensor (Mod (Cᵒᵖ ⥤ Ab.{u + 1}) (constRingObj (C := C) T))) :=
  NatIso.ofComponents
    (fun N₁ ↦ NatIso.ofComponents (fun N₂ ↦ toModTensorIso N₁ N₂) fun {N₂ N₂'} g ↦ by
      refine Mod.hom_ext _ _ (NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
        (LinearMap.ext fun x ↦ ?_)))
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        exact (congrArg (fun k ↦ (k.app U).hom (a ⊗ₜ[ℤ] b))
          (Mod.tensorObjπ_whiskerLeft (M := toMod T N₁) ((moduleToMod T).map g))).symm
      | add x y hx hy => simp_all)
    fun {N₁ N₁'} f ↦ by
      refine NatTrans.ext (funext fun N₂ ↦ Mod.hom_ext _ _ (NatTrans.ext (funext fun U ↦
        AddCommGrpCat.hom_ext_toIntLinearMap (LinearMap.ext fun x ↦ ?_))))
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        exact (congrArg (fun k ↦ (k.app U).hom (a ⊗ₜ[ℤ] b))
          (Mod.tensorObjπ_whiskerRight (N := toMod T N₂) ((moduleToMod T).map f))).symm
      | add x y hx hy => simp_all

end CategoryTheory.Presheaf
