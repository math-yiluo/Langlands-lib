# Presentation independence for the actual translated comparison

`ActualConjugateLeviCoherence.presentationIndependence` proves the
presentation-independence clause of `ClosedV32Statement`, the actual
translated coherence target for Waldspurger V.3.2 (printed p. 295,
PDF p. 61).

Both certified comparisons factor as the fixed actual unitary
translation followed by a common-Levi comparison on the target
side. The two common-Levi maps have the same target square-integrable
representation, split-central quotient Haar scale, compact and
parabolics. Apply the presentation-independence conclusion of
`ActualCommonLeviCoherence.closedCommonLeviCoherence` to identify the
two maps on the full unitary parameter group. Substitution in the
two factorization equalities gives equality of the original
translated comparisons.
