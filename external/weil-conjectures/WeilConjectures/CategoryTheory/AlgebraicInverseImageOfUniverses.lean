/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Algebraic inverse image along a morphism of topoi

Source: Stacks Project, Modules on Sites, Tag 03D2, and Sites, Tag 00YV;
Cohomology on Sites, Tag 06YY (auxiliary; not a blueprint node).

The underlying sheaves are identified with inverse images of sheaves of sets.
Operations are transported by requiring preservation of their graphs on generalized
sections. Taking the test sheaf to be the product of the operand sheaves recovers the
usual inverse-product-comparison formula. Constants use the terminal test sheaf.
These conditions determine the algebraic structures, including their additive inverses.
The coefficient universe `r` and module universe `m` are independent. Their underlying
sheaves are explicitly transported by `uliftFunctor` to `Type (max r m)`; every graph
condition descends through `ULift.down`. The sites have independent object and morphism
universes. The imported specialized presentation remains available for existing users.
-/

@[expose] public section

universe uC vC uD vD r m

open CategoryTheory

namespace SheafOfModules

/-- Algebraic lifts of an inverse-image functor, with all ring and module operations
transported along it. The natural underlying-sheaf isomorphism also fixes the action
on module morphisms. Graph equations are imposed for every test sheaf, so they apply
to the universal tuples of operands, not merely to global sections.
Source: Stacks Project, Modules on Sites, Tag 03D2, and Sites, Tag 00YV
(auxiliary; not a blueprint node). -/
structure AlgebraicInverseImageOfUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m, r})]
    [JC.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{m} ⋙ uliftFunctor.{r, m})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m, r})]
    [JD.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{m} ⋙ uliftFunctor.{r, m})]
    (L : Sheaf JC (Type (max r m)) ⥤ Sheaf JD (Type (max r m)))
    (R : Sheaf JC CommRingCat.{r}) (RI : Sheaf JD CommRingCat.{r}) where
  ringUnderlying : L.obj ((sheafCompose JC (CategoryTheory.forget CommRingCat.{r} ⋙
    uliftFunctor.{m, r})).obj R) ≅
    (sheafCompose JD (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m, r})).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type (max r m)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m,
      r})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x).down) =
        (@id (R.obj.obj U) (a.hom.app U x).down) + (@id (R.obj.obj U) (b.hom.app U x).down)) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x)).down) =
        (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x)).down) +
          (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)).down)
  ringMul : ∀ (T : Sheaf JC (Type (max r m)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m,
      r})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x).down) =
        (@id (R.obj.obj U) (a.hom.app U x).down) * (@id (R.obj.obj U) (b.hom.app U x).down)) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x)).down) =
        (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x)).down) *
          (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)).down)
  ringZero : ∀ (T : Sheaf JC (Type (max r m)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m, r})).obj
      R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x).down) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x)).down) = 0
  ringOne : ∀ (T : Sheaf JC (Type (max r m)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m, r})).obj
      R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x).down) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x)).down) = 1
  modules : SheafOfModules.{m}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{m}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RI)
  moduleUnderlying :
    modules ⋙ toSheaf _ ⋙ sheafCompose JD (CategoryTheory.forget AddCommGrpCat.{m} ⋙
      uliftFunctor.{r, m}) ≅
      (toSheaf _ ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{m} ⋙ uliftFunctor.{r,
        m})) ⋙ L
  moduleAdd : ∀ (M : SheafOfModules.{m}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf JC (Type (max r m))) (a b t : T ⟶
      ((toSheaf _ ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{m} ⋙ uliftFunctor.{r,
        m})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x).down) =
        (@id (M.val.obj U) (a.hom.app U x).down) + (@id (M.val.obj U) (b.hom.app U x).down)) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id ((modules.obj M).val.obj V) ((moduleUnderlying.inv.app M).hom.app V ((L.map t).hom.app
        V x)).down) =
        (@id ((modules.obj M).val.obj V) ((moduleUnderlying.inv.app M).hom.app V ((L.map
          a).hom.app V x)).down) +
          (@id ((modules.obj M).val.obj V) ((moduleUnderlying.inv.app M).hom.app V ((L.map
            b).hom.app V x)).down)
  moduleZero : ∀ (M : SheafOfModules.{m}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf JC (Type (max r m))) (a : T ⟶
      ((toSheaf _ ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{m} ⋙ uliftFunctor.{r,
        m})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (M.val.obj U) (a.hom.app U x).down) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id ((modules.obj M).val.obj V) ((moduleUnderlying.inv.app M).hom.app V ((L.map a).hom.app
        V x)).down) = 0
  moduleSMul : ∀ (M : SheafOfModules.{m}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (T : Sheaf JC (Type (max r m)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{r} ⋙ uliftFunctor.{m, r})).obj
      R))
    (b t : T ⟶ ((toSheaf _ ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{m} ⋙
      uliftFunctor.{r, m})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x).down) =
        (@id (R.obj.obj U) (a.hom.app U x).down) • (@id (M.val.obj U) (b.hom.app U x).down)) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id ((modules.obj M).val.obj V) ((moduleUnderlying.inv.app M).hom.app V ((L.map t).hom.app
        V x)).down) =
        (@id (RI.obj.obj V) (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x)).down) •
          (@id ((modules.obj M).val.obj V) ((moduleUnderlying.inv.app M).hom.app V ((L.map
            b).hom.app V x)).down)

end SheafOfModules
