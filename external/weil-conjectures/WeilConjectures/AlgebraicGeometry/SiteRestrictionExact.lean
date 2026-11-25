/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Exactness of restriction to a localized site

Source: Stacks Project, Sites, Section 00XZ (localized site and restriction);
Modules on Sites, localization section, surrounding Lemma 03DJ
(blueprint: lem-weil-pbc-site-restriction-exact).
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Restriction of abelian sheaves to the localized site is exact.

Source: Stacks Project, Sites, Section 00XZ; Modules on Sites, localization
(near Lemma 03DJ). (blueprint: lem-weil-pbc-site-restriction-exact)

Proof, step 1 (`def-weil-pbc-sites-and-cohomology`): for every slice object
`V ⟶ W`, restriction has section group `G(V)` and the original section maps.
A covering in the slice is precisely a covering of its underlying object.
Step 2: the sectionwise kernel of a map of abelian sheaves is a sheaf: a
compatible family glues in the source, and its image is zero by separatedness
of the target. Thus monomorphisms are sectionwise injective and middle exactness
is sectionwise equality of the image and kernel; both survive restriction.
By `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, the last map of a
short exact sequence is locally surjective. A covering `Vᵢ ⟶ V` providing lifts
also covers `V ⟶ W` in the slice, using the composites `Vᵢ ⟶ V ⟶ W`.
The same lemma on the slice makes the restricted last map an epimorphism.
Hence the restricted sequence is short exact.
-/
theorem siteRestriction_exact
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C)
    (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (J.toGrothendieck.overPullback AddCommGrpCat.{u} W)).ShortExact := by
  -- Restriction preserves limits and is also a left adjoint by cover lifting.
  let F := J.toGrothendieck.overPullback AddCommGrpCat.{u} W
  have : Limits.PreservesColimitsOfSize.{u, u} F :=
    ((Over.forget W).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.toGrothendieck.over W) J.toGrothendieck).leftAdjoint_preservesColimits
  exact hS.map_of_exact F

end CategoryTheory
