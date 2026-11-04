# The actual reductive relative Weyl quotient in rank at most one

Let `k : Type u` be any field, `G` a connected reductive group scheme, and
`i : T.toGrp ⟶ G` a maximal split torus. Suppose every pair of actual
adjoint roots is linearly dependent over the integers.
`IsConnectedReductive.rankOneRelativeWeylQuotientSignEmbedding` embeds the
actual rational Weyl quotient `relativeWeylGroup i = N(k)/Z(k)` in `Bool`.
`IsConnectedReductive.card_relativeWeylGroup_le_two_of_rankOne` concludes
that this quotient has at most two elements.

The published joint-spanning theorem
`relativeRootsRestrictedCharactersSpan` discharges the spanning input of
`IsSplitTorus.relativeWeylAction_injective_of_span`. This proves that the
actual quotient acts faithfully on the rational root span. The Mathlib
construction `MonoidHom.ofInjective` identifies it with its actual action
image. Composing this equivalence with the published
`IsSplitTorus.rankOneRelativeWeylSignEmbedding` gives the new embedding.
The latter encodes the identity by `true` and negation by `false`.
The cardinality bound follows by monotonicity under an injection into
`Bool`.

The `_of_isMaximalTorus` variants assume that `T` is split and that `i` is
maximal among all tori. They apply the same results using the published
comparison from a split maximal torus to a maximal split torus.

This module is an internal adapter of the published spanning, conditional
faithfulness and rank-one image results, with no further geometric or
root-system premise. Reductive affineness and smoothness provide the
instances needed by these results. It covers arbitrary characteristic,
the full universe `u`, and the empty root set. It does not prove that
actual roots are reduced, bound dimensions of quotient schemes, or prove
positive-root uniqueness.
