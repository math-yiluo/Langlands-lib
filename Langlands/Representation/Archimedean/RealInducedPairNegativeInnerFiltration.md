# Actual filtration in the negative-inner-weight outer-square region

This internal derived unit uses the actual negative-inner quotient and the
ascending exchange construction. It reuses Worker 765's rank-one assembly and
parity helpers from `RealInducedPairDistantFiltration` and
`RealInducedPairDistantParity`. No additional literature or image premise is used.

For linked complex character data `d,e` at the natural index `k`, write
`L=d.weight.natAbs`, `M=e.weight.natAbs`, `P=outerWeight d e k`, and
`H=innerWeight d e k`. The proposition
`RealInducedPairNegativeInnerFiltrationStatement` assumes `H<0` and
`L²+M²<P²`, and concludes the actual
`RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)`.
There is no hypothesis on the parity of the original data and no separate
positive-weight hypothesis; `H<0` implies both weights are positive.
`realInducedPairNegativeInnerFiltration` proves this proposition.

Choose `h=H.natAbs`, `sd=(h+L)%2`, `se=0`, and write `u,v,x,y` for the four
ascending presentation characters. The incoming ascending word has first
crossing the outer binomial, middle crossings generic on their actual parity
classes, and last crossing the inner tail with cutoff `h`. The arithmetic
parities follow from the choice of `sd` and `H+L+M=P`.

The last tail maps onto the actual middle-induced module
`J=[u,induced(pairInduced x v h),y]`. Its explicit inverse-tail section proves
surjectivity onto `J`. `last_factor` identifies its inclusion into the
four-character space with the last full-character Frobenius map, by equality
of compact Fourier coefficients. The two generic middle crossings are also
surjective. Composing their suffix with the actual original quotient is
therefore surjective by `RealInducedPairNegativeInnerQuotient.quotient_surjective`.
All maps in this suffix are exact intertwiners.

Now apply the two-piece rank-one decomposition at the first, outer crossing.
The full four-crossing word followed by the original quotient descends through
the source two-block quotient to an exact map from
`[.induced e,.induced d]`, with the same range. The outer inverse-tail section,
pushed through the suffix and quotient, intertwines modulo that descended
range. These two maps span the whole original module.
`filtration_of_pieces` proves this for an arbitrary predicate on these two
source lists.

The second source list is the actual mixed outer list
`[x,induced(pairInduced u y P),v]`. Its support is a permutation of the original
four endpoints, and its squared-weight sum is `P²`. The assumed strict
inequality makes it an allowed heavier piece; the first source is exactly the
allowed swapped pair. This verifies every clause of the regional adjacent
filtration.

The negative-inner region with `P²≤L²+M²` remains outside this statement. In
that region the mixed outer list is too light for this assembly and requires
further image elimination or refinement. The unrestricted filtration is not
asserted.
