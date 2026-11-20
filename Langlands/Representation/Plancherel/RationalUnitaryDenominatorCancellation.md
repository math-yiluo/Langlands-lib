# Cancelling a second denominator of a rational operator

`RationalUnitaryPoleFactorization.cancelFromCross` starts with a
`RationalOperatorContinuationData` for an operator on its original domain.
A second polynomial numerator and pole-factorable denominator satisfy a
global cross-multiplication identity with that continuation. The original
denominator is nonzero throughout the original domain. This gives the
cleared identity for the second numerator at every point of that domain,
including the zeros of the second denominator.

A per-vector norm bound for the original operator on its dense unitary
domain gives a bound for the cleared second numerator on the whole
unitary group. Apply the finite pole cancellation in the supplied normed
model of the target carrier. Divide the cross-multiplication identity
by the pole product on its dense nonzero locus and extend the identity
by polynomiality. The resulting numerator and remaining denominator
therefore clear the original operator everywhere their domains overlap.
One remaining denominator works for every input vector.

`ActualCommonLeviV3.exists_regularGermAt_of_poleFactorization_cross`
applies this construction to the actual compact comparison. The
nonzero locus of the remaining denominator is ambient open and
contains every unitary parameter. The cleared identity on its
intersection with the genuine generic locus gives the required local
representatives.

The construction adapts the cancellation argument in Waldspurger
(2003), Corollary V.2.3 and Lemma V.3.1, printed pp. 294–295 / PDF
pp. 60–61 (`waldspurger-2003-plancherel`), to a denominator obtained
separately from the original rational presentation. The pole
factorization, cross identity, and unitary bound are inputs.
