/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso

/-! # Componentwise transport between composition isomorphisms

Source: naturality and equality transport for functors.
(blueprint: def-weil-pbc-transported-composite-iso)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F₀ F₁ F₂ F₃ : C ⥤ D}

/-- Compose two natural isomorphisms by transporting their middle object componentwise.
Source: Mathlib's natural isomorphisms and eqToHom.
(blueprint: def-weil-pbc-transported-composite-iso). -/
def transportedCompositeIso (a : F₀ ≅ F₁) (b : F₂ ≅ F₃) (h : F₁ = F₂) : F₀ ≅ F₃ :=
  NatIso.ofComponents
    (fun K ↦ a.app K ≪≫ eqToIso (congrArg (fun F : C ⥤ D ↦ F.obj K) h) ≪≫ b.app K)
    (by
      cases h
      intro K L f
      simp)

/-- Componentwise transport is the usual composite with equality transport of functors.
Source: Mathlib's eqToHom_app.
(blueprint: lem-weil-pbc-transported-composite-iso-eq)
Proof. Substitute the equality of the middle functors. The inserted transports are
identities; the components of both composites coincide by the category identity laws.
-/
theorem transportedCompositeIso_eq (a : F₀ ≅ F₁) (b : F₂ ≅ F₃) (h : F₁ = F₂) :
    transportedCompositeIso a b h = a ≪≫ eqToIso h ≪≫ b := by
  cases h
  ext K
  simp [transportedCompositeIso]

end CategoryTheory
