# Basic facts on left reducedness

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Basic`.

## `leftReduced_of_isSubquotient` (clause 1 of the target)

If `Y'` is a subquotient of `Y` and `Y` is left `A`-reduced (in the sense of
`Langlands.Classification.LeftCuspidalDerivative.LeftReduced`), then `Y'` is left
`A`-reduced.

**Proof (as implemented).** Let `Z` be an irreducible subquotient of `Y'` that embeds into
`A × σ`. Subquotients compose (`SegmentHeadSupport.isSubquotient_trans`), so `Z` is an
irreducible subquotient of `Y`, contradicting left reducedness of `Y`. The finite-length
hypothesis of clause 1 of the target is not needed.
