# The weighted main-term integrand

`wavePacketPairExponent`, `wavePacketPairDenominator` and
`wavePacketPairMainTerm` give the summand of the truncated
Eisenstein pairing in terms of the two Weyl maps to each standard
target. The exponent uses conjugation on the second transported
parameter. The denominator is the product over the simple coroots
outside the target Levi. The numerator uses the coroot covolume,
the exponential at the truncation point and the pairings of the
two finite intertwining expansions.

`ae_wavePacketPairDenominator_ne_zero` combines almost-everywhere
nonvanishing of the individual factors over the finite target,
Weyl and coroot sets. It uses the product of coordinate Lebesgue
measure in the common central frequency and additive Haar measure
in each relative frequency. The statement uses actual first-input
Weyl conjugations, root presentations and target Levi retractions.

`WavePacketPairMainTermMeasurabilityStatement` concerns the main
term composed with a continuous map into the two coordinate spaces.
On the measured set its image lies in the two spectral sets, whose
imaginary parameters lie in the holomorphy domains of the
coefficients. The coefficients are continuous there by holomorphy
in coordinates. The evaluated exponents are continuous real
linear forms, so the phases and coroot products are measurable
everywhere. Inversion with its value at zero is measurable, and
finite sums and products give almost-everywhere strong measurability
for the measure restricted to the stated set.

The formulas are from E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, Clay Math. Proc. 13 (2011),
§3, p. 313 (volume PDF p. 322), formula (2), and §8, p. 328
(volume PDF p. 337), equation (18).
