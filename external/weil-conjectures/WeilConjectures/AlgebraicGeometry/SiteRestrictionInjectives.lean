/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact

/-!
# Extension by zero and restriction on a localized site

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Section 03DH
and Lemmas 03DI--03DJ (blueprint: lem-weil-pbc-site-restriction-injectives).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction to a localized site has an exact extension-by-zero left adjoint,
and is itself exact.

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Section 03DH
and Lemmas 03DI--03DJ (blueprint: lem-weil-pbc-site-restriction-injectives).

Proof:
1. Use the localized topology on `Over W`: a covering is one whose underlying
   family covers in `C`. Restriction evaluates a sheaf at the underlying object
   of each arrow to `W`, with its original restriction maps
   (`def-weil-pbc-sites-and-cohomology`, Stacks Sites, Section 00XZ).
2. Apply `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` to
   `Over.forget W`. This is `lem-weil-pbc-site-restriction-adjunction` and gives
   the natural adjunction between the displayed extension by zero and restriction.
3. Apply `site_extensionByZero_exact`
   (`lem-weil-pbc-site-extension-by-zero-exact`) to obtain one zero-morphism
   preservation witness and preservation of every short exact sequence on the slice.
4. Apply `siteRestriction_exact` (`lem-weil-pbc-site-restriction-exact`) to each
   short exact sequence on the original site. Combine the three conclusions.
-/
theorem siteRestriction_injectives
    {C : Type w} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    Nonempty
        (Functor.sheafPullbackConstruction.sheafPullback
            (Over.forget W) AddCommGrpCat.{w} (J.toGrothendieck.over W)
            J.toGrothendieck ⊣
          J.toGrothendieck.overPullback AddCommGrpCat.{w} W) ∧
      (∃ (hL : (Functor.sheafPullbackConstruction.sheafPullback
          (Over.forget W) AddCommGrpCat.{w} (J.toGrothendieck.over W)
          J.toGrothendieck).PreservesZeroMorphisms),
        ∀ (S : ShortComplex (Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{w})),
          S.ShortExact →
            (@ShortComplex.map _ _ _ _ _ _ S
              (Functor.sheafPullbackConstruction.sheafPullback
                (Over.forget W) AddCommGrpCat.{w}
                (J.toGrothendieck.over W) J.toGrothendieck) hL).ShortExact) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{w})),
        S.ShortExact →
          (S.map (J.toGrothendieck.overPullback AddCommGrpCat.{w} W)).ShortExact) := by
  refine ⟨⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget W) AddCommGrpCat (J.toGrothendieck.over W) J.toGrothendieck⟩, ?_, ?_⟩
  · exact site_extensionByZero_exact J W
  · intro S hS
    exact siteRestriction_exact J W S hS

end CategoryTheory
