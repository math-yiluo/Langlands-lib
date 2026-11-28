# Compact coefficient pairings and intertwining

Let \(K\) be a compact topological group with Borel Haar measure \(\mu\). Let
\(\rho,\sigma\) be finite-dimensional smooth complex representations of \(K\).
If every intertwiner from \(\rho\) to \(\sigma\) is zero, then for any linear
functionals \(a,b\) on their respective endomorphism spaces,
`compactCoefficientPairing` gives
\[
\int_K a(\rho(k^{-1}))\,b(\sigma(k))\,d\mu(k)=0.
\]

The representation on linear maps from the space of \(\rho\) to the space of
\(\sigma\) is smooth using common finite-dimensional fixing levels. Integrating this
action against the constant test takes values in the invariant subspace, which
consists of intertwiners. Applying the zero average to a rank-one linear map and
then taking a coefficient gives the vanishing for products of vector coefficients.
A basis expansion by columns expresses each endomorphism functional as a finite
sum of vector coefficients, so the same vanishing holds for \(a\) and \(b\).

This is the coefficient orthogonality used to relate compact interaction and
descent. See Clozel, *Characters of nonconnected, reductive p-adic groups*,
§3.4, Lemma 5, p. 154, and §3.6, Lemma 9, p. 158.
