/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Presentations of abelian inverse image

Source: Stacks Project, Sites, Section 00YR and Proposition 00YV (2)
(blueprint: def-trf-abelian-inverse-image-presentation).
-/

@[expose] public section

universe w uC vC uD vD

namespace CategoryTheory

/-- An abelian lift of a set-sheaf functor, normalized on every generalized section.
Source: Stacks Project, Sites, 00YR and 00YV (2)
(blueprint: def-trf-abelian-inverse-image-presentation).

The natural underlying-sheaf isomorphism fixes the maps as well as the objects.
The graph equations for addition and zero specify transport of those operations.
For a finite-limit-preserving functor, take the test sheaf to be the product of
operands, or the terminal sheaf for zero, to recover the product-comparison formula.
Negation is then forced by the addition and zero equations. No exactness or
adjunction on abelian sheaves is included in this definition. -/
structure AbelianInverseImagePresentation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) where
  /-- The functor on abelian sheaves. -/
  functor : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}
  /-- Its natural identification with `L` after forgetting the operations. -/
  underlying : functor ⋙ sheafCompose K (forget AddCommGrpCat.{w}) ≅
    sheafCompose J (forget AddCommGrpCat.{w}) ⋙ L
  /-- Addition is the transport of the original addition under `L`. -/
  map_add : ∀ (M : Sheaf J AddCommGrpCat.{w}) (T : Sheaf J (Type w))
    (a b t : T ⟶ (sheafCompose J (forget AddCommGrpCat.{w})).obj M),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      t.hom.app U x = @id (M.obj.obj U) (a.hom.app U x) +
        @id (M.obj.obj U) (b.hom.app U x)) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (underlying.inv.app M).hom.app V ((L.map t).hom.app V x) =
        @id ((functor.obj M).obj.obj V)
          ((underlying.inv.app M).hom.app V ((L.map a).hom.app V x)) +
        @id ((functor.obj M).obj.obj V)
          ((underlying.inv.app M).hom.app V ((L.map b).hom.app V x))
  /-- Zero is the transport of the original zero under `L`. -/
  map_zero : ∀ (M : Sheaf J AddCommGrpCat.{w}) (T : Sheaf J (Type w))
    (a : T ⟶ (sheafCompose J (forget AddCommGrpCat.{w})).obj M),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), @id (M.obj.obj U) (a.hom.app U x) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      @id ((functor.obj M).obj.obj V)
        ((underlying.inv.app M).hom.app V ((L.map a).hom.app V x)) = 0

end CategoryTheory
