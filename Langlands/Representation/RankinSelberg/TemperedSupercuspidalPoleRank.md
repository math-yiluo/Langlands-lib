# Rank bounds for a supercuspidal seed in a selected centered segment

Author: Worker 1743.

This internal module supplies the rank argument needed by
`TemperedTwistSupercuspidalPoleStatement`. It does not prove pole existence.
The content is derived from finite sums of positive block ranks,
irreducibility, and published evaluation equivalences for normalized
induction from a single block. No classification existence theorem or
L-factor formula is assumed or proved.

`SupercuspidalPoleRankBounds F τ a` is the conjunction of `a + 1 ≤ k` and
`a + 1 < k` when the source `τ` of rank `k` is not supercuspidal. It asserts
neither a partner nor an L-polynomial certificate.

`IsIrreducibleComponent.nonempty_equiv` proves that a component of an
irreducible representation is equivalent to the ambient representation,
with independent carrier universes. In a component presentation, the
subrepresentation cannot be zero, since it surjects onto a nonzero
irreducible representation. It is therefore the whole irreducible ambient
representation. The resulting surjective intertwiner has zero kernel by
irreducibility and is an equivalence.

`selectedCenteredSegment_rank_arithmetic` considers a selected block `i`
of a positive block shape of total rank `n`, and a centered segment of
length `d + 1` whose seed has rank `a + 1` and whose total rank is that block
rank. Then `a + 1 ≤ n`. If equality holds, the segment length is one,
and any second positive block would make the sum larger than `n`; hence the
block shape also has length one.

`centeredSegment_zero_equiv` identifies the normalized induction of a
length-one centered segment with its smooth seed, by the zero real twist
and the published single-block evaluation equivalence.

`selectedCenteredSegment_rankBounds` assumes an actual equivalence from
a normalized induction to the source, smoothness of its blocks, and a
selected block component presentation by a centered segment of an
irreducible supercuspidal seed. It applies the arithmetic result. In the
equality case, both inductions have one block. Their evaluation
equivalences and the component equivalence identify the source with the
supercuspidal seed. Supercuspidality transports across this actual
equivalence, so a source that is not supercuspidal has strictly larger
rank. The result requires no irreducibility or temperedness hypothesis on
the source beyond what its supplied equivalence and component data entail
in this equality case.
