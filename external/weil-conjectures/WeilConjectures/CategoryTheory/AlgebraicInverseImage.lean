/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
/-!
# Algebraic inverse image along a morphism of topoi
Source: Stacks Project, Modules on Sites, Tag 03D2, and Sites, Tag 00YV;
Cohomology on Sites, Tag 06YY (auxiliary; not a blueprint node).
The underlying sheaves are identified with inverse images of sheaves of sets.
Operations are transported by requiring preservation of their graphs on generalized
sections. Taking the test sheaf to be the product of the operand sheaves recovers the
usual inverse-product-comparison formula. Constants use the terminal test sheaf.
These conditions determine the algebraic structures, including their additive inverses.
-/
@[expose] public section
universe w uC vC uD vD
open CategoryTheory
namespace SheafOfModules
/-- Algebraic lifts of an inverse-image functor, with all ring and module operations
transported along it. The natural underlying-sheaf isomorphism also fixes the action
on module morphisms. Graph equations are imposed for every test sheaf, so they apply
to the universal tuples of operands, not merely to global sections.
Source: Stacks Project, Modules on Sites, Tag 03D2, and Sites, Tag 00YV
(auxiliary; not a blueprint node). -/
structure AlgebraicInverseImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (R : Sheaf JC CommRingCat.{w})
    (RI : Sheaf JD CommRingCat.{w}) where
  ringUnderlying : L.obj ((sheafCompose JC
      (CategoryTheory.forget CommRingCat.{w})).obj R) ≅
    (sheafCompose JD (CategoryTheory.forget CommRingCat.{w})).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type (w)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) +
          (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringMul : ∀ (T : Sheaf JC (Type (w)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) *
          (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringZero : ∀ (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1
  modules : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w}
        RingCat.{w})).obj R) ⥤
    SheafOfModules.{w}
      ((sheafCompose JD (forget₂ CommRingCat.{w}
        RingCat.{w})).obj RI)
  moduleUnderlying :
    modules ⋙ toSheaf _ ⋙ sheafCompose JD
      (CategoryTheory.forget AddCommGrpCat.{w}) ≅
      (toSheaf _ ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{w})) ⋙ L
  moduleAdd : ∀ (M : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w}
        RingCat.{w})).obj R))
    (T : Sheaf JC (Type (w))) (a b t : T ⟶
      ((toSheaf _ ⋙ sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x)) =
        (@id (M.val.obj U) (a.hom.app U x)) + (@id (M.val.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id ((modules.obj M).val.obj V)
        ((moduleUnderlying.inv.app M).hom.app V ((L.map t).hom.app V x))) =
        (@id ((modules.obj M).val.obj V)
        ((moduleUnderlying.inv.app M).hom.app V ((L.map a).hom.app V x))) +
          (@id ((modules.obj M).val.obj V)
        ((moduleUnderlying.inv.app M).hom.app V ((L.map b).hom.app V x)))
  moduleZero : ∀ (M : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w}
        RingCat.{w})).obj R))
    (T : Sheaf JC (Type (w))) (a : T ⟶
      ((toSheaf _ ⋙ sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (M.val.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id ((modules.obj M).val.obj V)
        ((moduleUnderlying.inv.app M).hom.app V ((L.map a).hom.app V x))) = 0
  moduleSMul : ∀ (M : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w}
        RingCat.{w})).obj R))
    (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R))
    (b t : T ⟶ ((toSheaf _ ⋙ sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) • (@id (M.val.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id ((modules.obj M).val.obj V)
        ((moduleUnderlying.inv.app M).hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) •
          (@id ((modules.obj M).val.obj V)
        ((moduleUnderlying.inv.app M).hom.app V ((L.map b).hom.app V x)))
end SheafOfModules
