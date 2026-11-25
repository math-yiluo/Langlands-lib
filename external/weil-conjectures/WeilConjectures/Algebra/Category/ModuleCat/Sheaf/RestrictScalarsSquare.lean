/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Restriction of scalars along a commutative square of ring sheaves

For morphisms of sheaves of rings with `α ≫ β = γ ≫ δ`, restricting scalars along `β` and then
`α` agrees with restricting along `δ` and then `γ`; the comparison is the identity on sections.

Source: Stacks Project, Tag 03DA.
-/

@[expose] public noncomputable section

universe v u₀ v₀ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  {A B B' D : Sheaf J RingCat.{u}} (α : A ⟶ B) (β : B ⟶ D) (γ : A ⟶ B') (δ : B' ⟶ D)
/-- Restriction of scalars along the two sides of a commutative square of ring sheaves agree,
by the identity on sections. -/
def restrictScalarsSquareIso (h : α ≫ β = γ ≫ δ) :
    restrictScalars.{v} β ⋙ restrictScalars.{v} α ≅
      restrictScalars.{v} δ ⋙ restrictScalars.{v} γ :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget A).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
          ((α ≫ β).hom.app U).hom rfl (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsComp'App (γ.hom.app U).hom (δ.hom.app U).hom
          ((α ≫ β).hom.app U).hom
          (by rw [h]; rfl) (M.val.obj U))
      (fun {U V} f ↦ by ext x; rfl)))
    (fun _ ↦ by ext U x; rfl)

@[simp]
lemma restrictScalarsSquareIso_hom_app_val_app (M : SheafOfModules.{v} D) (U : Cᵒᵖ)
    (x : M.val.obj U) (h : α ≫ β = γ ≫ δ) :
    ((restrictScalarsSquareIso α β γ δ h).hom.app M).val.app U x = x :=
  rfl


/-- Restricting scalars along `β` and then along a section `α` of it is the identity, by the
identity on sections. -/
def restrictScalarsCancelIso (α : A ⟶ B) (β : B ⟶ A) (h : α ≫ β = 𝟙 A) :
    restrictScalars.{v} β ⋙ restrictScalars.{v} α ≅ 𝟭 (SheafOfModules.{v} A) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget A).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
          (RingHom.id (A.obj.obj U))
          (congrArg RingCat.Hom.hom (NatTrans.congr_app
            (congrArg (fun k : A ⟶ A ↦ k.hom) h) U)).symm (M.val.obj U)).symm ≪≫
        (ModuleCat.restrictScalarsId (A.obj.obj U)).app (M.val.obj U))
      (fun {U V} f ↦ by ext x; rfl)))
    (fun _ ↦ by ext U x; rfl)

/-- Restriction of scalars along an isomorphism of ring sheaves is an equivalence. -/
theorem restrictScalars_isEquivalence_of_isIso (f : A ⟶ B) [IsIso f] :
    (restrictScalars.{v} f).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (restrictScalars.{v} f) (restrictScalars.{v} (inv f))
    (restrictScalarsCancelIso (inv f) f (IsIso.inv_hom_id f)).symm
    (restrictScalarsCancelIso f (inv f) (IsIso.hom_inv_id f))).isEquivalence_functor

end SheafOfModules
