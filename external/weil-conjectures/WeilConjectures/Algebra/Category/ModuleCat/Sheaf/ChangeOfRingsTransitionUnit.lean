/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition

/-!
# The transition between changes of rings and the tensor units

For `γ = α ≫ β`, the transition `M ⊗_{R₁} R₂ ⟶ M ⊗_{R₁} R₃` sends `1 ⊗ m` to `1 ⊗ m`. Hence,
for scalar-extension adjunctions whose units are `m ↦ 1 ⊗ m`, the unit along `α` followed by
the transition is the unit along `γ`, up to the identification of the composite restriction.

Source: Stacks Project, Tag 03EK.
-/

@[expose] public section

universe v₀ u₀ u

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

set_option hygiene false in
local notation "𝓕" f => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map f

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

variable {R₁ R₂ R₃ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) (γ : R₁ ⟶ R₃)
  (h : α ≫ β = γ)
  {E₂ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₂)}
  {E₃ : SheafOfModules.{u} (𝓡 R₁) ⥤ SheafOfModules.{u} (𝓡 R₃)}
  (h₂ : ∀ M, E₂.obj M = changeOfRings α M)
  (hm₂ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₂.map a = eqToHom (h₂ M) ≫ changeOfRingsHom α M a ≫ eqToHom (h₂ N).symm)
  (h₃ : ∀ M, E₃.obj M = changeOfRings γ M)
  (hm₃ : ∀ {M N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N),
    E₃.map a = eqToHom (h₃ M) ≫ changeOfRingsHom γ M a ≫ eqToHom (h₃ N).symm)

/-- If the units of `E₂ ⊣ res_α` and `E₃ ⊣ res_γ` are `m ↦ 1 ⊗ m` and
`e : res_β ⋙ res_α ≅ res_γ` is the identity on sections, then the unit along `α` followed by
the transition is the unit along `γ` followed by `e⁻¹`.
Proof: evaluate on a section `m`; the transition sends `1 ⊗ m` to `β 1 ⊗ m = 1 ⊗ m`. -/
theorem changeOfRingsTransitionOfEq_unit (adj₂ : E₂ ⊣ restrictScalars (𝓕 α))
    (adj₃ : E₃ ⊣ restrictScalars (𝓕 γ))
    (hu₂ : ∀ (M : SheafOfModules.{u} (𝓡 R₁)) (U : Cᵒᵖ) (x : M.val.obj U),
      (adj₂.unit.app M).val.app U x = (eqToHom (h₂ M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app U
          ((1 : R₂.obj.obj U) ⊗ₜ[R₁.obj.obj U,(α.hom.app U).hom] x)))
    (hu₃ : ∀ (M : SheafOfModules.{u} (𝓡 R₁)) (U : Cᵒᵖ) (x : M.val.obj U),
      (adj₃.unit.app M).val.app U x = (eqToHom (h₃ M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf γ M).presheaf).app U
          ((1 : R₃.obj.obj U) ⊗ₜ[R₁.obj.obj U,(γ.hom.app U).hom] x)))
    (e : restrictScalars (𝓕 β) ⋙ restrictScalars (𝓕 α) ≅ restrictScalars (𝓕 γ))
    (he : ∀ (M : SheafOfModules.{u} (𝓡 R₃)) (U : Cᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x)
    (M : SheafOfModules.{u} (𝓡 R₁)) :
    adj₂.unit.app M ≫ (restrictScalars (𝓕 α)).map
        ((changeOfRingsTransitionOfEq α β γ h h₂ hm₂ h₃ hm₃).app M) =
      adj₃.unit.app M ≫ e.inv.app (E₃.obj M) := by
  ext U x
  have hi : (e.hom.app (E₃.obj M)).val.app U ((e.inv.app (E₃.obj M)).val.app U
      ((adj₃.unit.app M).val.app U x)) = (adj₃.unit.app M).val.app U x :=
    congrArg (fun f ↦ f.val.app U ((adj₃.unit.app M).val.app U x))
      (e.inv_hom_id_app (E₃.obj M))
  rw [he] at hi
  refine ((congrArg (((changeOfRingsTransitionOfEq α β γ h h₂ hm₂ h₃ hm₃).app M).val.app U)
    (hu₂ M U x)).trans ?_).trans hi.symm
  rw [changeOfRingsTransitionOfEq_tmul, map_one, hu₃]

end SheafOfModules
