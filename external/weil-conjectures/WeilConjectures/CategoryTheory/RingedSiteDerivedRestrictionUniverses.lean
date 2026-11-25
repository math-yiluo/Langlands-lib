/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction

/-!
# Slice restriction with independent site and coefficient universes

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r m w w'

open CategoryTheory

namespace CategoryTheory

/-- Restrict the canonical localization representative and localize on the slice.
This is the recorded construction, with independent object, Hom and coefficient sizes.
Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(auxiliary; not a blueprint node). -/
def ringedSiteDerivedRestrictionOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify (J.over U) AddCommGrpCat.{m}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasDerivedCategory.{w} (SheafOfModules.{m} R)]
    [HasDerivedCategory.{w'} (SheafOfModules.{m} (R.over U))]
    (K : DerivedCategory (SheafOfModules.{m} R)) :
    DerivedCategory (SheafOfModules.{m} (R.over U)) :=
  letI := module_overFunctor_preservesZero R U
  DerivedCategory.Q.obj
    (((SheafOfModules.overFunctor.{m} R U).mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage K))

end CategoryTheory
