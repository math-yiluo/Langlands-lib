/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteLocalization

/-!
# RingedSiteCompleteElement

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- The local vanishing criterion R internal Hom(O_U[1/f], K|U) = 0.
The localization is placed in degree zero. IsZero means the derived object
is zero, with no boundedness, coherence or finite-generation assumption.
The local instance only reconciles the definitionally equal presentations
of the slice ring sheaf (forgetting commutativity before or after slicing).

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998
(auxiliary; not a blueprint node). -/
def IsRingedSiteCompleteElement {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (U : C) (f : R.obj.obj (op U)) : Prop :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
  IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSiteSectionLocalization ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U f)),
    ringedSiteDerivedRestriction ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U K))

end CategoryTheory
