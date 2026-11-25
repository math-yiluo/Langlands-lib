/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Pairwise compatibility of components of a descent morphism

Source: Stacks Project, Tag 01ZR (3), agreement on overlaps.
(blueprint: def-pc-local-map-pair-compatibility). -/

@[expose] public section

open CategoryTheory
namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type*} [Category* C]
  {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
  {D₁ D₂ : P.DescentData f}

/-- Compatibility of a component family on one ordered pair.
Source: Stacks Project, Tag 01ZR (3), agreement on overlaps.
(blueprint: def-pc-local-map-pair-compatibility).

The field is exactly the universal-test descent square for this pair. The
structure contains only a proof of that square and introduces no chosen data. -/
structure PairCompatibility (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι) : Prop where
  comm ⦃W : C⦄ (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t) :
    (P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂ =
      D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b)

/-- Assemble the morphism from its component family and all pairwise squares.
Source: Stacks Project, Tag 01ZR (3), Zariski gluing.
Proof: use r as the hom field; the required comm field for a and b is the
comm field of h a b. The descent-data category imposes no further conditions. -/
def homOfPairCompatibility (r : ∀ a, D₁.obj a ⟶ D₂.obj a)
    (h : ∀ a b, PairCompatibility r a b) : D₁ ⟶ D₂ where
  hom := r
  comm W t a b g₁ g₂ h₁ h₂ := (h a b).comm (W := W) t g₁ g₂ h₁ h₂

/-- The assembly preserves the prescribed components.
Proof: the component field of the constructor is r, so this is reflexivity. -/
theorem homOfPairCompatibility_hom (r : ∀ a, D₁.obj a ⟶ D₂.obj a)
    (h : ∀ a b, PairCompatibility r a b) (a : ι) :
    (homOfPairCompatibility r h).hom a = r a := rfl


end CategoryTheory.Pseudofunctor.DescentData
