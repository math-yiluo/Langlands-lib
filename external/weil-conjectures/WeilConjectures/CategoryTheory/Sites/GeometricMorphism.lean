/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Geometric morphisms and their 2-morphisms

Source: ILO, Exposé XI §1.1 and §1.4; Stacks Project, Sites, Tag 00XA
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open Limits

/-- An adjunction with left exact inverse image. When its two categories are topoi,
this is a geometric morphism. Source: Stacks, Tag 00XA; ILO XI §1.1
(auxiliary; not a blueprint node). -/
structure GeometricMorphism (E : Type u₁) (F : Type u₂)
    [Category.{v₁} E] [Category.{v₂} F] where
  inverse : F ⥤ E
  direct : E ⥤ F
  adj : inverse ⊣ direct
  leftExact : PreservesFiniteLimits inverse

namespace GeometricMorphism

variable {E : Type u₁} {F : Type u₂} {G : Type u₃}
  [Category.{v₁} E] [Category.{v₂} F] [Category.{v₃} G]

/-- Composition of geometric morphisms. Source: ILO XI §1.4
(auxiliary; not a blueprint node). -/
def comp (a : GeometricMorphism E F) (b : GeometricMorphism F G) :
    GeometricMorphism E G where
  inverse := b.inverse ⋙ a.inverse
  direct := a.direct ⋙ b.direct
  adj := b.adj.comp a.adj
  leftExact := by
    have := a.leftExact
    have := b.leftExact
    exact comp_preservesFiniteLimits _ _

/-- The inverse-image mate of a 2-morphism, whose defining direction is on direct images.
Source: ILO XI §1.3 (auxiliary; not a blueprint node). -/
noncomputable def inverseMate {a b : GeometricMorphism E F} (t : a.direct ⟶ b.direct) :
    b.inverse ⟶ a.inverse :=
  (conjugateEquiv a.adj b.adj).symm t

/-- The inverse-image isomorphism corresponding to a direct-image isomorphism.
Source: ILO XI §1.4 (auxiliary; not a blueprint node). -/
noncomputable def inverseIso {a b : GeometricMorphism E F} (t : a.direct ≅ b.direct) :
    b.inverse ≅ a.inverse :=
  (conjugateIsoEquiv a.adj b.adj).symm t

end GeometricMorphism
end CategoryTheory
