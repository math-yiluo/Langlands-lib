/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# RingedSiteDerivedRestriction

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- Restriction of a derived object K to the slice site C/U, computed by
restricting the canonical representative DerivedCategory.Q.objPreimage K
and applying Q on the slice. This represents K|U: slice restriction is exact,
as expressed by localizedModule_restriction_quasiIso. No boundedness is used.
The existing module_overFunctor_preservesZero supplies the complex functor.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(auxiliary; not a blueprint node). -/
noncomputable def ringedSiteDerivedRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    (K : DerivedCategory (SheafOfModules.{u} R)) :
    DerivedCategory (SheafOfModules.{u} (R.over U)) :=
  letI := module_overFunctor_preservesZero R U
  DerivedCategory.Q.obj
    (((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage K))

end CategoryTheory
