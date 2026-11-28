# Transfer of the spectral main-term limit to full wave packets

`WavePacketApproximatePairingLimitStatement` combines the two analytic
steps of Lapid's proof of Proposition 2 in §8. Its data are a full
quotient measure and a measure on the norm-one quotient, with a
measure-preserving product chart using coordinate Lebesgue measure for
the centre. The spectral charts carry the given locally finite relative
measures and central Lebesgue measure to full coordinate Lebesgue measure.
The passive measure on the norm-one quotient is s-finite. The two
finite families have continuous coefficient functions vanishing outside
their respective compact supports.

Eventually along the given filter, the norm-one families are almost
everywhere strongly measurable for the restricted product measures.
Each family member has square-integrable fibres with a bound on their
squared norms that is uniform in the compact spectral support. This
bound may depend on the filter parameter. The full integrands in the
quotient chart are the corresponding weighted norm-one sums multiplied
by the positive central phase. The weighted approximation is almost
everywhere strongly measurable on the equal-frequency support. For each
pair of family indices the difference between the exact norm-one
pairing and its approximation is bounded almost everywhere on that
support by an error tending to zero.

`wavePacketApproximatePairingLimit` uses the compact fibre bounds to obtain
joint square integrability of the weighted norm-one integrands and then
applies `wavePacketFourierPairing`. This gives eventual square integrability
of both full wave packets and expresses their pairing as the iterated
equal-frequency pairing times
\((2\pi)^m / ((2\pi)^n (2\pi)^{n'})\), with \(m\) central coordinates and
\(n,n'\) full spectral coordinates. The filter bounds for the finitely many
errors apply simultaneously. `compactSpectralPairingError` shows that the
iterated integral of the difference tends to zero. Multiplying by the
same fixed normalization and adding the given limit of the normalized
approximating integrals proves the limit of the full pairing.

The Fourier step and substitution of the main term come from E. Lapid,
*On Arthur's asymptotic inner product formula of truncated Eisenstein
series*, Clay Math. Proc. 13 (2011), §8, p. 328 (volume PDF p. 337).
The statement takes the fibre bounds, phase, uniform pairing errors and
limit of (18) as hypotheses.
