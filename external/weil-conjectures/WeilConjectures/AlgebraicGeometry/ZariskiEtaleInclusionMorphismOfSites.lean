/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Sheaf
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleSheafLeftExact

/-!
# The inclusion of the Zariski site into the small étale site

Source: literature/stacks-project/sites.tex, Proposition Tag 00X6 and
Lemma Tag 00X5 (blueprint: lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites)

## Main statements

* `zariski_to_etale_is_morphism` records the inclusion functor, its continuity,
  preservation of finite limits, and exact sheaf inverse image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- The inclusion of the Zariski site into the small étale site is a morphism of sites.

Source: literature/stacks-project/sites.tex, Proposition Tag 00X6 and
Lemma Tag 00X5 (blueprint: lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites).
Proof (the seven steps of the node):
1. Open immersions are étale (`lem-weil-pbc-open-immersion-etale`), so send an
   open to its inclusion and an inclusion to the corresponding morphism over `X`.
   Identities and composition are those of inclusions.
2. The top open is terminal, and intersections are pullbacks in the poset of opens
   (`lemma-uniform-bounds-pro-etale-affines`).
3. The identity of `X` is terminal in the small étale site, and its pullbacks are
   scheme pullbacks (`situation-conventions`). Intersections
   compute these pullbacks by `lem-weil-pbc-open-preimage-fibre-product`; uniqueness
   of limits gives the canonical comparison isomorphisms.
4. A jointly surjective open family remains jointly surjective and étale. Together
   with step 3 this gives Stacks continuity (`def-weil-pbc-sites-and-cohomology`).
5. Precomposition sends sheaves to sheaves
   (`lem-weil-pbc-site-continuous-pushforward-sheaf`). Sheafified presheaf pullback
   is its left adjoint (`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`),
   hence preserves colimits (`situation-conventions`).
6. The inclusion of sheaves preserves finite limits
   (`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`); presheaf pullback does too,
   by steps 2 and 3 (`situation-conventions`), as does
   sheafification (`situation-conventions`). Their composite is
   the left adjoint, so it preserves finite limits.
7. This exact left adjoint and sectionwise precomposition give the required
   morphism of sites, inverse image, direct image and adjunction
   (`def-weil-pbc-sites-and-cohomology`).
-/
theorem zariski_to_etale_is_morphism (X : Scheme.{u}) :
    ∃ (i : X.Opens ⥤ X.Etale),
      (i ⋙ Scheme.Etale.forget X = X.restrictFunctor) ∧
      CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i ∧
      PreservesFiniteLimits i ∧
      Nonempty (IsTerminal (i.obj ⊤)) ∧
      ∃ (_ : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology),
        ∃ (L : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) ⥤
            Sheaf X.smallEtaleTopology (Type (max (u + 1) v))),
          Nonempty (L ⊣ i.sheafPushforwardContinuous (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) ∧
          PreservesFiniteLimits L ∧ PreservesFiniteColimits L := by
  obtain ⟨i, hi_forget, hi_cover, hi_limits, hi_terminal, hcont⟩ :=
    zariski_to_etale_core X
  obtain ⟨hcontinuous, hflat⟩ := hcont
  let : RepresentablyFlat i := hflat
  let L := i.sheafPullback (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  have hLlim : PreservesFiniteLimits L := zariski_to_etale_sheaf_left_exact X i hcontinuous
  have : L.IsLeftAdjoint :=
    (i.sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).isLeftAdjoint
  have hLcolim : PreservesFiniteColimits L := inferInstance
  exact ⟨i, hi_forget, hi_cover, hi_limits, hi_terminal,
    ⟨hcontinuous, L, ⟨i.sheafAdjunctionContinuous (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology⟩, hLlim, hLcolim⟩⟩

end AlgebraicGeometry
