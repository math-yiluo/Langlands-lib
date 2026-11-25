/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Bounded-below injective resolutions on a small ringed site

Source: Stacks Project, Cohomology on Sites, Section 21.19 (Tag 07A5), using
Injectives, Theorem 19.12.6 (Tag 079P)
(blueprint: lem-sc-bounded-below-injective-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- Every bounded-below complex of modules on a small ringed site admits a quasi-isomorphism
into a bounded-below complex with injective terms which is also K-injective.

Source: Stacks Project, Tags 07A5 and 079P, with the bounded-below replacement furnished by
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`
(blueprint: lem-sc-bounded-below-injective-resolution).

Proof:
1. The category of module sheaves on a small ringed site is Grothendieck abelian by the
Grothendieck assertion of `lem-pur-ringed-site-grothendieck-abelian`, supplied directly
by the proved upstream `SheafOfModules.isGrothendieckAbelian`. Mathlib's
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` then supplies enough injectives.
2. Choose a lower bound for `G`. Apply the unbundled Mathlib theorem
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`, the construction
underlying `lem-sc-bounded-below-injective-resolution-existence`. This gives a complex
`I`, strictly supported above the same lower bound, with injective terms and a
quasi-isomorphism `G ⟶ I`, without packaging it in the category of injective objects.
3. Apply `lem-weil-pbc-bounded-below-injectives-kinjective`
(`CochainComplex.isKInjective_of_injective`) to conclude that `I` is K-injective. -/
theorem exists_boundedBelow_injective_resolution
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hG : ∃ n : ℤ, G.IsStrictlyGE n) :
    ∃ (I : CochainComplex
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (i : G ⟶ I),
      QuasiIso i ∧ (∃ n : ℤ, I.IsStrictlyGE n) ∧
        (∀ n : ℤ, Injective (I.X n)) ∧ I.IsKInjective := by
  have := isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  obtain ⟨n, hn⟩ := hG
  have : G.IsStrictlyGE n := hn
  obtain ⟨I, i, hi, hI, hIn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective G n
  have : I.IsStrictlyGE n := hIn
  have : ∀ q : ℤ, Injective (I.X q) := hI
  exact ⟨I, i, hi, ⟨n, hIn⟩, hI, CochainComplex.isKInjective_of_injective I n⟩

end SheafOfModules
