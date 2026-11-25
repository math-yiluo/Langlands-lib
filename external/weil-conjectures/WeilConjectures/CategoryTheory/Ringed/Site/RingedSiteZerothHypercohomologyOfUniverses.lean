/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-!
# Zeroth hypercohomology with independent site universes

Source: Stacks Project, Sections 07A5 and 08JA
(blueprint: def-pur-ringed-site-zeroth-hypercohomology).

The original construction is retained by the public import. This companion composes the
same right derived global sections functor with zeroth homology on the actual ringed site.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite

namespace CategoryTheory

/-- `H⁰ RΓ` on a ringed site, with module sections in a universe containing its objects,
arrows and ring sections. Global sections are `Hom_R(R, -)`; the right derived functor
uses the canonical functorial K-injective replacement, followed by zeroth homology.
No representative or site equivalence is chosen by an unspecified existence theorem.

Source: Stacks Project, Section 07A5 and Lemma 08JA
(blueprint: def-pur-ringed-site-zeroth-hypercohomology). -/
noncomputable def ringedSiteZerothHypercohomologyOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
      AddCommGrpCat.{max c v r} :=
  letI : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v r}
  let Γ : SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤ AddCommGrpCat.{max c v r} :=
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
  Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0

end CategoryTheory
