# Left reducedness of segment products

Module `Langlands.Representation.Classification.MoeglinWaldspurgerDatumReduced`.

`datum_leftReduced`: assuming `LeftCuspidalDerivativeLemma`, if every block of a
segment-product datum has finite length and is left `A`-reduced (for a supercuspidal `A` of
positive rank), then the full product is left `A`-reduced and has finite length. Proof by
strong induction on the number of blocks: no blocks (rank zero, vacuous since `d > 0`, finite
length via the published unit isomorphism `zeroDatumUnitIso`); one block (the published
`singletonIso`); otherwise the published splitting `SegmentProductSplit.nonempty_iso_binary`
into the first block and the remaining product, and the product clause of the lemma.
`leftReduced_rankCast` and `hasFiniteLength_rankCast` transport these properties along
`Derivative.generalLinearRankCast`.
