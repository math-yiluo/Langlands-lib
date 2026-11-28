# Compact spectral tests of characteristic truncated pairings

`truncatedPairing_compactSpectralTest` exchanges a compactly supported continuous
spectral test with the characteristic integral on the norm-one rational quotient.
It assumes a jointly continuous family and a continuous tested form, both left
invariant under rational points. Their evaluations at quotient representatives
descend to continuous functions by the open quotient map. The characteristic
region is compact under the rational covering hypothesis for the Siegel factors.
The product of this region and the support of the test gives an integrable
function for the two restricted measures. Fubini gives the exchange, and the
test vanishes outside its support. The lemma also gives spectral integrability
of the tested truncated pairing for each truncation parameter.

`characteristicSpectralTestLimit` proves `CharacteristicSpectralTestLimitStatement`.
Fix a nonzero vector \(v\) in the relative coroot span with every simple root
strictly positive on \(v\). The truncation regions at \(T=k v\), \(k\in\mathbb N\),
exhaust the norm-one quotient provided every class lies in some characteristic
region for the fixed Siegel data. The finite set of simple roots gives a
uniform margin \(\delta>0\) along the ray, so each root is eventually above
the regularity threshold and is bounded below by \(\delta\|T\|\). The norm
here is taken in the specified real truncation coordinates.

The family can be restricted along a continuous map from the spectral test
space before integrating. If the full tested pairing is integrable, exhaustion
and the Fubini lemma give convergence of the tested characteristic pairings to
the full integral. Assume the regularized function on the imaginary axis is
continuous at each regular truncation parameter and satisfies the stated
exponential comparison with the characteristic pairing at the trivial central
translate on each bounded spectral set. The regularized tests are then
eventually integrable. On the compact support, the tested difference is bounded
by the product of the test's supremum norm, the support measure and the
uniform exponential error. This bound tends to zero along the ray and gives
the same limit for the regularized pairings.

The exchange and limit implement the opening of the proof of Lemma 7.11 in
Patrick Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023), 109107, p. 35. The exponential comparison at the trivial central
translate is the specialization of Theorem 7.1, p. 25, used there. The registered
PDF in `delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
