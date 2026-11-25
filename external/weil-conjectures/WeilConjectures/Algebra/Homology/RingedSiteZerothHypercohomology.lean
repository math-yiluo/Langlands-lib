/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Zeroth hypercohomology on a small ringed site

Source: Stacks Project, Cohomology on Sites, Section 07A5 and Lemma 08JA
(blueprint: def-pur-ringed-site-zeroth-hypercohomology).
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

/-- The functor `H⁰(C, -) = H⁰ RΓ(C, -)` on the unbounded derived category of a small
ringed site. Here `Γ = Hom_O(O, -)` is `preadditiveCoyoneda` at the unit module.

Source: Stacks Project, Cohomology on Sites, Section 07A5 and Lemma 08JA
(blueprint: def-pur-ringed-site-zeroth-hypercohomology).

The Grothendieck property (`prop-pur-kinjective-resolutions-exist`) is the proved
`SheafOfModules.isGrothendieckAbelian`, as in `derivedInternalHom`. The existing
`Functor.rightDerivedFunctorObjQIso` computes `RΓ` on any K-injective representative
by applying `Γ` termwise. Applying `DerivedCategory.homologyFunctorFactors` gives
`H⁰(Γ(J))`, with the canonical independence of the representative supplied by the
right derived functor. The target derived category uses its standard localization;
its morphism universe has no effect on the resulting abelian group. -/
noncomputable def ringedSiteZerothHypercohomology
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤ AddCommGrpCat.{u} :=
  haveI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0

end CategoryTheory
