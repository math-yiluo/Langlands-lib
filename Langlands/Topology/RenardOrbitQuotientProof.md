# Proofs of Renard II.3.3–II.3.4

This module proves the unchanged published proposition
`Langlands.Topology.RenardOrbitQuotient.Statements` in
`Langlands/Topology/RenardOrbitQuotientStatements.lean`. The closing theorem
`Langlands.Topology.RenardOrbitQuotient.statements` retains the two independent
universe parameters `uG` and `uX`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are II.3.3, printed p.44 / PDF p.50, and its Corollary
and II.3.4, printed p.45 / PDF p.51. Both pages were read. The statement
pair records the necessary nonemptiness correction for open-orbit existence;
the proof adds no further hypotheses.

The implementation proves the six conjuncts as follows.

1. `finiteOrbitOpenOrbit` uses the existing Library theorem
   `Langlands.Topology.FiniteOrbitProof.exists_relOpen_orbit` on the closed
   invariant set `univ`. Its nonemptiness follows from the target's
   `Nonempty X`. The resulting relatively open orbit is open in `X`.
   The helper `isOpenMap_smul_of_open_orbit` regards this orbit as an open
   subspace, hence locally compact Hausdorff and Baire, with its induced
   continuous transitive action. Mathlib's
   `isOpenMap_smul_of_sigmaCompact` proves openness into this orbit at every
   point; composing with the open subtype inclusion proves the ambient-space
   formula required by the target.
2. `finiteOrbitsLocallyClosed` uses the published
   `Langlands.Topology.finiteOrbitOrdering`. If the orbit of `x` has index
   `i`, it is the difference between the open initial union through `i`
   and the preceding open initial union. Pairwise disjointness proves this
   set equality, expressing the orbit as an open set intersected with a
   closed set. The argument starts with an arbitrary `x`, so it handles
   empty spaces without imposing nonemptiness.
3. `invariantQuotientImages` proves that the inverse image of the image of
   an invariant subset is the subset itself. Mathlib's
   `MulAction.isOpenQuotientMap_quotientMk` supplies the open continuous
   quotient projection on the exact quotient in the statement. Closedness
   descends through the quotient-map criterion. For local closedness, use
   the criterion that the coborder `(closure Z \ Z)ᶜ` is open. Coborders
   commute with inverse images under continuous open maps
   (`coborder_preimage`); saturation then reduces the quotient criterion
   to the assumed local closedness of `Z`.
4. The internal helper `locallyProfinite_of_openQuotientMap` proves that an
   open continuous surjection from a locally profinite space to a Hausdorff
   space has locally profinite target. Given a target neighborhood, choose
   a preimage of its base point, then a compact open neighborhood inside
   its inverse image. Its image is compact by continuity, open by openness,
   contains the target point and lies inside the prescribed neighborhood.
   `hausdorffOrbitQuotient` applies this directly to the actual orbit
   projection. This is the compact-open-neighborhood argument of the
   paragraph following II.3.3's Lemma.
5. `transitiveQuotientHomeomorphism` uses Mathlib's actual map
   `MulAction.ofQuotientStabilizer G x`. It is injective by the
   orbit-stabilizer theorem, surjective by transitivity, continuous by the
   subgroup quotient topology and open by the open mapping theorem applied
   to the transitive action. These properties give a homeomorphism whose
   value on `QuotientGroup.mk g` is definitionally `g • x`, proving the
   exact canonical-map requirement.
6. `closedSubgroupQuotient` uses Mathlib's Hausdorff instance
   `QuotientGroup.instT2Space`, proved via properness of the action of a
   closed subgroup. The subgroup quotient projection is an open quotient
   map, so the helper in item 4 applies. No normality assumption is used.

The auxiliary lemmas are internal consequences of the cited Library and
Mathlib APIs, introduced to share the implemented arguments. The finite-orbit
proof route reuses the Library's countable compact-cover and Baire argument;
it does not repeat Renard's compact open subgroup construction. The
closed-subgroup Hausdorff proof reuses Mathlib's proper-action theorem in
place of the source's closed-diagonal argument. The source t.d. predicate
remains exactly `Langlands.Topology.IsLocallyProfinite` throughout.
