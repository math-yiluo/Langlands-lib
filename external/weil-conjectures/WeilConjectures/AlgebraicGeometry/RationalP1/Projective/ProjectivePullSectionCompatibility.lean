/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Compatibility with the two diagonal pullback sections -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory
namespace AlgebraicGeometry.ProEtale.RationalP1

/-- Compatibility with two section identifications, for arbitrary functors.
In the application the functors are the two pullbacks and restriction to the diagonal.
The proposition has just the displayed equation as its field. Passing the functors
explicitly keeps their derived-category interfaces fixed during specialization. -/
structure PullSectionCompatibility
    {C D : Type*} [Category C] [Category D]
    (F₁ F₂ : C ⥤ D) (G : D ⥤ C)
    (s₁ : F₁ ⋙ G ≅ 𝟭 C) (s₂ : F₂ ⋙ G ≅ 𝟭 C)
    (M : C) (t : F₂.obj M ⟶ F₁.obj M) : Prop where
  comm : G.map t ≫ s₁.hom.app M = s₂.hom.app M

end AlgebraicGeometry.ProEtale.RationalP1
