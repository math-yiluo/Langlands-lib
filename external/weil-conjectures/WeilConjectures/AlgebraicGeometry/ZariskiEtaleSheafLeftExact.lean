/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Sheaf

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- Left exactness of the canonical sheaf pullback, with arbitrary coefficient universe.

Source: Stacks Project, Sites, Lemma Tag 00X5, using Tags 00X3 and 00WJ.
(blueprint: lem-weil-pbc-zariski-etale-sheaf-left-exact)

Proof in words: representable flatness says that the category of arrows T -> i(U)
is cofiltered for each etale object T. Its opposite is therefore filtered. The
left Kan extension along i.op, evaluated at T, is the colimit of the original
presheaf over this opposite category. Finite limits of presheaves are computed
objectwise, and filtered colimits of sets commute with finite limits. This holds
also for sets in the larger universe max (u + 1) v: the indexing category is
small in that universe, and the elementwise filtered-colimit proof is unchanged.
In particular the empty finite limit is preserved because a filtered category
is nonempty and connected. Thus this presheaf pullback preserves finite limits.
The inclusion of sheaves into presheaves preserves limits, and sheafification
preserves finite limits (00WJ). Their composite with the presheaf pullback is
left adjoint to precomposition on sheaves by continuity. Uniqueness of left
adjoints identifies this composite with i.sheafPullback, so the latter preserves
finite limits as well. -/
theorem zariski_to_etale_sheaf_left_exact
    (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    (hcont : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
    [RepresentablyFlat i] :
    PreservesFiniteLimits (i.sheafPullback (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) := by
  let := hcont
  let : AB5OfSize.{u, u} (Type (max (u + 1) v)) :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  let := preservesFiniteLimits_op_lan_of_flat
    (H := Type (max (u + 1) v)) i
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

end AlgebraicGeometry
