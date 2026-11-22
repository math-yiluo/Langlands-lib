# Approximation in entire complex pair normalizations

Consider a sequence of complex pair integrals with their entire normalized
functional equations and strip-exponential growth. Assume all ordinary and
dual integrals are holomorphic on a common right half-plane and each sequence
is uniformly Cauchy on every vertical line there. Given the pointwise limit
of the ordinary integrals on that half-plane, `complexPairNormalizedApproximation`
proves locally uniform convergence of the entire ordinary normalizations
and identifies their limit on the half-plane.

The identity theorem moves the individual normalization formulas to the
common holomorphic half-plane. On a right boundary line the reciprocal
L-denominator multiplies the Cauchy estimate. For a left boundary line, the
functional equation reflects to a right boundary line of the dual sequence.
The dual denominator and the inverse signed epsilon factor both have
strip-exponential growth. `entireStripExtension` uses
Phragmén–Lindelöf on the two boundary estimates to give the locally uniform
entire limit, including its strip growth. Uniqueness of limits gives the
ordinary formula.

This is a derived limit argument for the continuity used in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), Theorem 2.3, author pp. 8–9.
It uses the two line estimates of Jacquet’s proof of Proposition 4.1 in
§4.2, author pp. 22–25, in sequential form with both raw traces as inputs.
