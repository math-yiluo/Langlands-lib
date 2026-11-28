# Integrated error for compact spectral pairings

`equalFrequencyPair` evaluates two real linear charts at a common central
frequency and at independent relative frequencies.
`isCompact_equalFrequencySupport` shows that the inverse image of the product
of two compact supports under this map is compact. It is closed by continuity
and lies in the product of three compact coordinate projections obtained from
the inverse charts.

`CompactSpectralPairingErrorStatement` concerns finite families of
continuous scalar coefficients vanishing off those compact supports. The
central frequency carries coordinate Lebesgue measure, and the two relative
frequencies carry locally finite Borel measures. The pairing in the passive
variable is the integral of the weighted left family times the conjugate of
the weighted right family. A second integrand replaces each individual
pairing by a specified approximation. Along the given filter the exact
pairing must eventually be integrable in the three spectral variables, the
approximation must be almost everywhere strongly measurable on the compact
support, and the individual fibres there must be square integrable for the
passive measure. For each pair of indices the error is bounded almost
everywhere on that support by a scalar depending only on the filter parameter
and tending to zero.

`compactSpectralPairingError` proves that the approximation is eventually
integrable and that the difference of the iterated integrals tends to zero.
The proof uses Hölder's inequality to expand the pairing as a finite sum of
individual integrals. It bounds each coefficient on its compact support and
sums the corresponding bounds for the errors. The exact pairing and its
approximation vanish when either frequency lies outside its coefficient
support. The product of the three spectral measures assigns finite mass to
the compact set where both supports are met. Integrating the bound there
gives integrability and an error estimate with that mass as a fixed factor.
Two applications of Fubini give the integrals in central, left relative and
right relative frequency order.

This is the measure-theoretic step in Lapid's replacement of the exact
truncated pairing by expression (18). The individual asymptotic estimates
enter as the hypotheses on the errors. See E. Lapid, *On Arthur's asymptotic
inner product formula of truncated Eisenstein series*, Clay Math. Proc. 13
(2011), §8, p. 328 (volume PDF p. 337), and §3, Proposition 1, formula (2),
p. 313 (volume PDF p. 322).
