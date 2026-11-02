# Actual transport of one original segment occurrence

Worker 320's internal conditional theorem `segmentOccurrenceToFront` assumes
`TwoSegmentHeadCommutation` for the supplied prime, field, topology and
independent universes. It does not prove that two-factor input. Given actual
strong heads in a segment-product datum, it moves a specified original
occurrence to the front whenever that segment is unlinked with every original
predecessor. The conclusion is an isomorphism of the full actual normalized
upper induced products, using the inverse of `Fin.cycleRange` to record the
resulting order.

The proof applies `Combinatorics.moveOccurrenceToFront` with the invariant
that the current induced product is isomorphic to the original one. The
permitted relation is unlinkage of the segments at the original labels.
At each step, the current permuted datum retains its supplied strong heads.
`AdjacentSegmentSwapLifting` identifies the actual merged two-block datum and
its two segment labels. The assumed two-factor commutation supplies the
isomorphism of that merged product, and the published lifting theorem gives
an isomorphism of the whole current product with its adjacent permutation.
Composition preserves the invariant. The final permutation moves precisely
the selected original label; repeated segments and their actual supplied
blocks remain separate occurrences.

This is an internal composition of finite permutation transport and actual
induction regrouping. It introduces no classification, irreducibility or
analytic conclusion and supplies no unconditional segment commutation proof.
