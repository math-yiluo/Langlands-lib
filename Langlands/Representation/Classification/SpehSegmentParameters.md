# Segment parameters of Speh representations

This derived construction uses the centered exponents in the published
`SpehDatum`, together with the published special-segment and Langlands-head
classification results. It supplies a parameter and elementary comparison
lemmas; it does not assert binary product occurrence.

`spehSegmentMultisegment Δ k` lists the twists `ν^((k-1)/2-i) Δ`, for
`0 ≤ i < k`. Its degree is `k * Δ.degree`. The two successor recurrences
separate the largest exponent from the list. They imply that for `k ≥ 1`
the sum of the two opposite half-twists equals the sum of the parameters
of lengths `k+1` and `k-1`.

`SpehDatum.segmentProductDatum` retains the supplied discrete-series
representation as every block, transported through the segment degree equality.
Its normalized induction equals the original centered Speh induction. Its
segments have decreasing twist exponents, and integral twist freeness excludes
a forbidden precedence. Twisting the supplied special head proves that each
block is the head of its segment. Finally, strong-head existence for the
centered tempered standard module and the actual Speh quotient-uniqueness
clause show that every supplied Speh representative is a Langlands head of
this multisegment.

The parameter is the segment version of `a(δ,k)` just before Tadić 1986,
Theorem A.8, printed p.375 (registered source `tadic-1986-unitary`, PDF page 42).
The source's abstract block parameter is represented here using any actual
segment with special head `δ`; the established segment classification supplies
such a segment for an essentially square-integrable block. The proof uses the
Library's real-twist compatibility, integral twist freeness, regular Langlands
head existence and elementary actual target transport. It makes no unitarity
claim about Speh representations or their products.
