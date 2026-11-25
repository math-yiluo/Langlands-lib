/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses

/-!
# Exact left adjunction for restriction to a localized ringed site

Source: Stacks Project, Tags 03DI, 03DJ and 08FI.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For a sheaf of rings `R` on a Grothendieck site and an object `U`, assuming the
localized restriction functor preserves zero morphisms, there is a functor `G` from
localized `R`-module sheaves to `R`-module sheaves preserving finite limits and finite
colimits, together with an adjunction `G ⊣ restriction`, and the localized restriction
functor is additive.

Proof: for a localized module sheaf N, form the presheaf whose sections at V are
the direct sum of N(V,f) over arrows f : V to U, and sheafify it. Restrictions
send the f-summand to the composite-arrow summand using N's restriction map.
A map from this presheaf into a module sheaf M is equivalent to a map N to
M restricted to C/U: restrict to each summand in one direction, and sum the
component maps in the other. These operations are inverse and natural, and
sheafification gives the adjunction. The construction is additive. A monomorphism
of localized sheaves is injective on every section, so its presheaf extension
is injective on each direct sum. Exact module sheafification preserves this
monomorphism. As an additive left adjoint the extension is right exact;
preservation of monomorphisms therefore makes it exact. An exact additive
functor between abelian categories preserves finite limits and finite colimits.
Restriction preserves addition sectionwise.

Source: Stacks Project, Tags 03DI and 03DJ, the exact left adjoint used in
Tag 08FI, Lemma 21.20.1.
(auxiliary; not a blueprint node)
-/
theorem localized_restriction_adjunctionOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v r} R U).PreservesZeroMorphisms) :
    ∃ (G : SheafOfModules.{max u v r} (R.over U) ⥤ SheafOfModules.{max u v r} R),
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      (SheafOfModules.overFunctor.{max u v r} R U).Additive ∧
      Nonempty (G ⊣ SheafOfModules.overFunctor.{max u v r} R U) := by
  obtain ⟨G, hlim, hcolim, hadj⟩ :=
    localized_restriction_extension_existsOfUniverses.{u, v, r} R U hzero
  refine ⟨G, hlim, hcolim, ?_, hadj⟩
  constructor
  intro X Y f g
  ext V x
  rfl

end CategoryTheory
