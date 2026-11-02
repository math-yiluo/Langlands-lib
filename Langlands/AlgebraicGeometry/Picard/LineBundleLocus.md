# The rank-one locus and its full-fibre base open

For an actual module sheaf `M` on any `Scheme.{u}`, `rankOneLocus M` is
the open union of all open subsets on which `M` is isomorphic to the
structure sheaf. The membership lemma gives precisely a neighbourhood
and an actual restriction isomorphism. The locus is invariant under
module-sheaf isomorphism, and it is the whole scheme exactly when
`IsLocallyFreeRankOne M` holds.

`preimage_rankOneLocus_le` proves forward containment under arbitrary
scheme pullback. Its proof pulls a trivialization back to the inverse-image
open, using `restrictPullbackIso` and `pullbackUnitIso`. Consequently a
morphism whose image lies in this locus pulls `M` back to a line bundle.
The restriction/pullback comparison gives the actual line bundle
`lineBundleOnRankOneLocus M`, as well as restrictions to smaller opens.

For a universally closed morphism `f : X ⟶ S`, `rankOneBaseOpen f M`
is the complement in `S` of the image of the complement of
`rankOneLocus M`. The image is closed by Mathlib's
`Scheme.Hom.isClosedMap`. In particular the construction applies to every
proper morphism. A point of this base open is exactly a point whose full
set-theoretic fibre lies in the rank-one locus; an empty fibre satisfies
this condition. `le_rankOneBaseOpen_iff` is the corresponding universal
property for open subsets of `S`. The module restricts to the actual
line bundle `lineBundleOverRankOneBaseOpen f M` above this base open.
For any commuting square over a morphism with image in this base open,
`isLocallyFreeRankOne_pullback_over_baseOpen` proves that the actual
module pullback is locally free of rank one. In particular this supplies
the forward implication for every scheme base change into the base open.

These are elementary internal constructions from the published local
rank-one definition and pullback construction. Their role in the atlas
proof is the proper-image step in Stacks Project, Lemma 99.10.1,
[Tag 0D03](https://stacks.math.columbia.edu/tag/0D03).
The implemented construction directly uses rank one, rather than first
passing to all finite ranks and then removing the other ranks.
Registered source: `stacks-picard-stack-algebraicity-2026-11-01`,
content SHA-256
`f152eeac350ef0fb061c6651f63b2a7cdeb5d175ad92aacbf99e5e9f6eb0b0e0`,
retained file `0D03.txt`, proof of Lemma 99.10.1.

This file makes no finite-presentation or flatness assumption on `M`.
It proves forward containment under pullback, without asserting the
converse for an arbitrary base change. In particular it does not yet
identify a base-change test for line bundles, prove openness of the
Picard substack in a coherent-sheaf stack, or construct a smooth atlas.
Those claims need further hypotheses and proofs. All schemes and
morphisms retain universe `u`; there is no restriction to field-valued,
reduced, noetherian or quasi-compact tests.
