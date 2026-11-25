/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Transition maps between changes of rings

For morphisms of sheaves of commutative rings `α : R₁ ⟶ R₂`, `β : R₂ ⟶ R₃` and
`γ = α ≫ β`, and a sheaf of `R₁`-modules `M`, this file constructs the `R₂`-linear map
`M ⊗_{R₁} R₂ ⟶ M ⊗_{R₁} R₃` (with `R₃` regarded as an `R₂`-algebra through `β`) sending
`s ⊗ m` to `β s ⊗ m`.

Source: Stacks Project, Tag 03EK.
-/

@[expose] public section

universe v₀ u₀ u

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable {R₁ R₂ R₃ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) (γ : R₁ ⟶ R₃)
  (h : α ≫ β = γ) (M : SheafOfModules.{u} (𝓡 R₁))

include h in
set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise transition `s ⊗ m ↦ β s ⊗ m` exists. -/
theorem exists_changeOfRingsTransitionMap (X : Cᵒᵖ) :
    ∃ g : (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (β.hom.app X).hom).obj
        ((ModuleCat.extendScalars (γ.hom.app X).hom).obj (M.val.obj X)),
      ∀ (s : R₂.obj.obj X) (m : M.val.obj X),
        g (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
          β.hom.app X s ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m := by
  let : Module (R₁.obj.obj X) (R₃.obj.obj X) :=
    Module.compHom (R₃.obj.obj X) (γ.hom.app X).hom
  let T := (ModuleCat.restrictScalars (β.hom.app X).hom).obj
    ((ModuleCat.extendScalars (γ.hom.app X).hom).obj (M.val.obj X))
  have hγ (r : R₁.obj.obj X) : β.hom.app X (α.hom.app X r) = γ.hom.app X r := by
    rw [← h]
    rfl
  let k : M.val.obj X ⟶ (ModuleCat.restrictScalars (α.hom.app X).hom).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (α.hom.app X).hom).obj T)
      { toFun := fun m ↦ (1 : R₃.obj.obj X) ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m
        map_add' := by
          intro m n
          simp [TensorProduct.tmul_add]
        map_smul' := by
          intro r m
          change (1 : R₃.obj.obj X) ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] (r • m) =
            β.hom.app X (α.hom.app X r) •
              ((1 : R₃.obj.obj X) ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m)
          rw [hγ]
          change (1 : R₃.obj.obj X) ⊗ₜ[R₁.obj.obj X]
            ((show R₁.obj.obj X from r) • (show M.val.obj X from m)) = _
          rw [TensorProduct.tmul_smul]
          rfl }
  refine ⟨ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (α.hom.app X).hom k, ?_⟩
  intro s m
  let : Module (R₁.obj.obj X) T := Module.compHom T (α.hom.app X).hom
  let : Module (R₁.obj.obj X) (R₂.obj.obj X) :=
    Module.compHom (R₂.obj.obj X) (α.hom.app X).hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change β.hom.app X s •
    ((1 : R₃.obj.obj X) ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
/-- The sectionwise transition `s ⊗ m ↦ β s ⊗ m`. -/
noncomputable def changeOfRingsTransitionMap (X : Cᵒᵖ) :
    (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (β.hom.app X).hom).obj
        ((ModuleCat.extendScalars (γ.hom.app X).hom).obj (M.val.obj X)) :=
  Classical.choose (exists_changeOfRingsTransitionMap α β γ h M X)

theorem changeOfRingsTransitionMap_tmul (X : Cᵒᵖ) (s : R₂.obj.obj X) (m : M.val.obj X) :
    changeOfRingsTransitionMap α β γ h M X (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
      β.hom.app X s ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m :=
  Classical.choose_spec (exists_changeOfRingsTransitionMap α β γ h M X) s m

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

local instance changeOfRingsTransitionRestrictedModule {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Module (R₁.obj.obj Y)
      ((ModuleCat.restrictScalars ((𝓡 R₁).obj.map f).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (R₁.obj.obj Y) (M.val.obj Y))

private theorem changeOfRingsMap_tmul' {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : R₂.obj.obj X) (m : M.val.obj X) :
    changeOfRingsMap α M f (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
      R₂.obj.map f s ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m :=
  Classical.choose_spec (exists_changeOfRingsMap α M f) s m

set_option backward.isDefEq.respectTransparency false in
/-- The transition `s ⊗ m ↦ β s ⊗ m` between sectionwise changes of rings. -/
noncomputable def changeOfRingsPresheafTransition :
    changeOfRingsPresheaf α M ⟶
      (PresheafOfModules.restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).map β).hom).obj (changeOfRingsPresheaf γ M) where
  app X := changeOfRingsTransitionMap α β γ h M X
  naturality {X Y} f := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change changeOfRingsTransitionMap α β γ h M Y (changeOfRingsMap α M f _) =
      changeOfRingsMap γ M f (changeOfRingsTransitionMap α β γ h M X _)
    rw [changeOfRingsMap_tmul', changeOfRingsTransitionMap_tmul,
      changeOfRingsTransitionMap_tmul, changeOfRingsMap_tmul']
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise transition followed by the sheafification unit, as a map of presheaves of
modules into the restricted change of rings. -/
noncomputable def changeOfRingsTransitionUnit :
    changeOfRingsPresheaf α M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (𝓡 R₂).obj)).obj
        ((SheafOfModules.forget _).obj ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map β)).obj
            (changeOfRings γ M))) :=
  PresheafOfModules.homMk
    (((PresheafOfModules.toPresheaf _).map (changeOfRingsPresheafTransition α β γ h M) :
        (changeOfRingsPresheaf α M).presheaf ⟶ (changeOfRingsPresheaf γ M).presheaf) ≫
      toSheafify J (changeOfRingsPresheaf γ M).presheaf)
    (fun X r m ↦ by
      change ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R₃).obj)).unit.app
          (changeOfRingsPresheaf γ M)).app X
          ((changeOfRingsPresheafTransition α β γ h M).app X (r • m)) = _
      rw [((changeOfRingsPresheafTransition α β γ h M).app X).hom.map_smul]
      exact (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R₃).obj)).unit.app
          (changeOfRingsPresheaf γ M)).app X).hom.map_smul _ _)

/-- The `R₂`-linear transition `M ⊗_{R₁} R₂ ⟶ M ⊗_{R₁} R₃` sending `s ⊗ m` to `β s ⊗ m`,
for `γ = α ≫ β`. -/
noncomputable def changeOfRingsTransition :
    changeOfRings α M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map β)).obj (changeOfRings γ M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 R₂).obj)).symm
    (changeOfRingsTransitionUnit α β γ h M)

/-- The transition on sheafified pure tensors. -/
theorem changeOfRingsTransition_tmul (X : Cᵒᵖ) (s : R₂.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsTransition α β γ h M).val.app X
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app X
          (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m)) =
      (toSheafify J (changeOfRingsPresheaf γ M).presheaf).app X
        (β.hom.app X s ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m) := by
  have := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def (𝟙 (𝓡 R₂).obj)
    (changeOfRingsTransition α β γ h M)
  rw [changeOfRingsTransition, Equiv.apply_symm_apply] at this
  have := congrArg (fun φ ↦ φ.app X (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m)) this
  refine this.symm.trans ?_
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R₃).obj)).unit.app
      (changeOfRingsPresheaf γ M)).app X
      (changeOfRingsTransitionMap α β γ h M X (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m)) = _
  rw [changeOfRingsTransitionMap_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Change of rings of a morphism on sheafified sections. -/
theorem changeOfRingsHom_toSheafify {N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N) (X : Cᵒᵖ)
    (x : (changeOfRingsPresheaf α M).obj X) :
    (changeOfRingsHom α M a).val.app X
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app X x) =
      (toSheafify J (changeOfRingsPresheaf α N).presheaf).app X
        ((ModuleCat.extendScalars (α.hom.app X).hom).map (a.val.app X) x) := by
  have := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ({ app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U)
       naturality := changeOfRingsHom_naturality α M a } :
      changeOfRingsPresheaf α M ⟶ changeOfRingsPresheaf α N))
  exact (congrArg (fun φ ↦ φ.app X x) this).symm

set_option backward.isDefEq.respectTransparency false in
/-- The transition is natural in the module. -/
@[reassoc]
theorem changeOfRingsTransition_naturality {N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N) :
    changeOfRingsHom α M a ≫ changeOfRingsTransition α β γ h N =
      changeOfRingsTransition α β γ h M ≫ (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map β)).map
          (changeOfRingsHom γ M a) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 R₂).obj)).injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def,
    PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  ext X x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
    change (changeOfRingsTransition α β γ h N).val.app X
        ((changeOfRingsHom α M a).val.app X
          ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app X
            (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m))) =
      (changeOfRingsHom γ M a).val.app X ((changeOfRingsTransition α β γ h M).val.app X
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app X
          (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m)))
    rw [changeOfRingsHom_toSheafify, changeOfRingsTransition_tmul]
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [changeOfRingsTransition_tmul, changeOfRingsHom_toSheafify]
    erw [ModuleCat.ExtendScalars.map_tmul]

section OfEq

variable {E₂ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₂)}
  {E₃ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₃)}
  (h₂ : ∀ M, E₂.obj M = changeOfRings α M)
  (hm₂ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₂.map a = eqToHom (h₂ M) ≫ changeOfRingsHom α M a ≫ eqToHom (h₂ N).symm)
  (h₃ : ∀ M, E₃.obj M = changeOfRings γ M)
  (hm₃ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₃.map a = eqToHom (h₃ M) ≫ changeOfRingsHom γ M a ≫ eqToHom (h₃ N).symm)

/-- The transition between functors which compute the changes of rings on objects and
morphisms. -/
noncomputable def changeOfRingsTransitionOfEq :
    E₂ ⟶ E₃ ⋙ SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map β) where
  app M := eqToHom (h₂ M) ≫ changeOfRingsTransition α β γ h M ≫
    (SheafOfModules.restrictScalars _).map (eqToHom (h₃ M).symm)
  naturality M N a := by
    rw [hm₂, Functor.comp_map, hm₃]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Functor.map_comp, eqToHom_map, changeOfRingsTransition_naturality_assoc]

/-- The transition between functors computing the changes of rings, on sheafified pure
tensors. -/
theorem changeOfRingsTransitionOfEq_tmul (M : SheafOfModules.{u} (𝓡 R₁)) (X : Cᵒᵖ)
    (s : R₂.obj.obj X) (m : M.val.obj X) :
    ((changeOfRingsTransitionOfEq α β γ h h₂ hm₂ h₃ hm₃).app M).val.app X
        ((eqToHom (h₂ M).symm).val.app X
          ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app X
            (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m))) =
      (eqToHom (h₃ M).symm).val.app X
        ((toSheafify J (changeOfRingsPresheaf γ M).presheaf).app X
          (β.hom.app X s ⊗ₜ[R₁.obj.obj X, (γ.hom.app X).hom] m)) := by
  have e : (eqToHom (h₂ M).symm ≫ (changeOfRingsTransitionOfEq α β γ h h₂ hm₂ h₃ hm₃).app M) =
      changeOfRingsTransition α β γ h M ≫
        (SheafOfModules.restrictScalars _).map (eqToHom (h₃ M).symm) := by
    simp [changeOfRingsTransitionOfEq]
  have := congrArg (fun f ↦ f.val.app X
    ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app X
      (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m))) e
  refine this.trans ?_
  change (eqToHom (h₃ M).symm).val.app X ((changeOfRingsTransition α β γ h M).val.app X _) = _
  rw [changeOfRingsTransition_tmul]

end OfEq

end SheafOfModules
