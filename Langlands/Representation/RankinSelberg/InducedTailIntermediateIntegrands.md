# Actual zero-row integrands in the intermediate lower-block chart

This internal adapter connects the published definitions in
`RankinSelberg.QuotientIntegrals` with the block matrices used in the
intermediate-rank comparison. It is derived bookkeeping for the JPSS §9.3
argument, rather than a new assertion from the source.

`full_unequalRankFunction_lowerBlockPair` unfolds the actual full zero-row
function. Its large Whittaker coefficient is transported along the numerical
rank equality. The proof uses `whittakerRankCast_apply` and
`lowerBlockLocalization_eq_outer_appendIdentity` to identify its evaluation
matrix with the full localization matrix. The test coefficient and determinant
weight retain their actual arguments.

`full_unequalRankIntegrand_lowerBlockPair` gives the same equality for the
descended integrand at the quotient class of that matrix.
`reversedTail_unequalRankIntegrand` applies the existing same-function character
recasts to the actual zero-row tail integrand at the scaled character.
`reversedTail_unequalRankIntegrand_of_gap_eq` writes the positive test-to-tail
rank gap as `k+1` and transports the test coefficient to the precise index of
that tail integrand. Its identity-extension evaluation is proved entry by
entry in `inverseWhittakerRankCast_appendIdentity`.

These are pointwise identities. They provide no quotient chart, disintegration,
convergence, continuation, or span inclusion.
