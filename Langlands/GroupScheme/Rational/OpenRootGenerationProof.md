# Open root and centralizer subgroups generate an open subgroup

Author: Worker 4614.

`Langlands.GroupScheme.RelativeRoot.openRootCentralizerGeneration` proves
exactly the published proposition `OpenRootCentralizerGenerationStatement.{u}`
in [`OpenRootGenerationStatement`](OpenRootGenerationStatement.md), at
arbitrary universe `u`. The target pair and all of its imports are unchanged.

## What is proved

Fix any nonarchimedean local field `F : Type u`, a connected reductive group
`G` over `Spec F` with witness `hG`, a maximal split torus `i : S.toGrp ⟶ G`,
and a closed subgroup `j : Z ⟶ G` representing the actual torus centralizer
`torusCentralizer i`. Give `G(F)` and `Z(F)` the canonical
`rationalPointTopology`, and each actual root group
`U_a(F) = (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))` the subspace
topology from `G(F)`. For every family `V a` of subgroups indexed by all actual
relative roots, with `V a ≤ U_a(F)` and `V a` open in `U_a(F)`, and every open
subgroup `Z'` of `Z(F)`, the subgroup `Z'.map (rationalPoints.map j) ⊔ ⨆ a, V a`
of `G(F)` is open. This is the target `OpenRootCentralizerGeneration hG i j hj`
for every such datum.

Nothing in the target is weakened or strengthened. The theorem carries no
open-cell, root-product decomposition, integral-model, compactness or
topology-comparison hypothesis; the divisible and multipliable roots stay in
the index set.

## Implemented proof

The proof is a single application of two published theorems.

1. [`openRootCentralizerGeneration_of_dynamicRootOrderedProduct`](OpenRootGenerationReduction.md)
   proves `OpenRootGenerationFromOrderedProducts.{u}`, which is by definition
   the implication
   `DynamicRootOrderedProductStatement.{u} → OpenRootCentralizerGenerationStatement.{u}`.
   It obtains an open identity neighborhood of `G(F)` from the opposite open
   cell for a generic cocharacter, using the ordered root products of the
   premise to control both unipotent radicals, and concludes because a subgroup
   containing an identity neighborhood is open.
2. [`dynamicRootOrderedProduct`](DynamicRootOrderedProductProof.md) proves
   `DynamicRootOrderedProductStatement.{u}` with no premises: over every field
   and for every cocharacter, the product scheme of closed representatives of
   the full actual root subgroups, for any injective enumeration of the
   indivisible roots positive on the cocharacter, is isomorphic to a closed
   representative of the actual Dynamic radical, compatibly with the ordered
   multiplication map.

Applying the first theorem to the second gives the target at the same universe
`u`. Both supplied theorems have their full universe-general statements and no
extra premise, so the closing theorem has exactly the target's hypotheses.

## Provenance

This module is an internal composition of the published proofs named above and
adds no new mathematical assertion. Their authors and sources are listed in the
linked Markdown files. The mathematical target is Kaletha--Prasad,
*Bruhat--Tits Theory: A New Approach* (2023), Corollary 8.2.6, printed p.291 /
PDF p.322 (registered source `kaletha-prasad-2023-bruhat-tits-new-approach`),
with the local-field specialization and topology conventions documented in the
unchanged target Markdown. The source derives the corollary from Theorem
8.2.5(2), that is from the open cell (Proposition 2.11.3) and the ordered root
products (Theorem 2.11.15); the Lean route follows the same structure through
the two theorems above.
