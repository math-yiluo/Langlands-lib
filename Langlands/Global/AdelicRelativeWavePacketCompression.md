# Transferring standard-parabolic completeness to the split-centre quotient

`StandardWavePacketCompletenessStatement` uses full imaginary parameters on the rational quotient `G(F) \ G(𝔸)`. It fixes a minimal parabolic `p₀` with an Iwasawa compact `K` and tests every `IsParabolicWavePacket` of every presented parabolic above `p₀`. A square-integrable function pairing to zero with those tests is zero almost everywhere for `rationalQuotientHaarMeasure`.

`WavePacketSquareIntegrabilityStatement` asserts that every `IsWavePacket` representative is in `L²` for `rationalQuotientHaarMeasure`, with the same group, compact, matrix and minimal-parabolic hypotheses as `WavePacketRapidDecayStatement`.

`relativeWavePacketCompleteness_of_standard_of_squareIntegrable` takes `StandardWavePacketCompletenessStatement`, `WavePacketSquareIntegrabilityStatement` and `EisensteinContinuationAmbientShiftStatement.{0}` and concludes `RelativeWavePacketCompletenessStatement`. The ambient shift is used at imaginary parameters in the supplied holomorphy domain of each continuation.

`relativeWavePacketCompleteness_of_standard` proves `RelativeWavePacketCompletenessTransferStatement`. It obtains square integrability from `WavePacketRapidDecayStatement` at exponent zero by `wavePacketSquareIntegrability_of_rapidDecay`.

## Proof

The canonical split torus provides its positive subgroup and a product presentation of the rational quotient. The proof composes `measurePreserving_rationalQuotientDecomposition` with the inverse of `measurePreserving_canonicalNormOneQuotientHomeomorph`. The factor measures are the normalized positive Haar and the existing `canonicalMeasure` on `[G]`. Choose a measurable set `S` of positive finite measure in the positive subgroup. Lift `f` from `[G]` to the product by `(a, y) ↦ 1_S(a) f(y)`. This function is square integrable. Fubini and Cauchy–Schwarz show that the central integral of an `L²` function over `S` is in `L²([G])` and that its pairing with `f` equals the original pairing with the lift.

For a full packet of a fixed presentation, use `relativeAmbientParameterEquiv` to express the full real spectral coordinates as a pair `(x, z)` of relative and ambient coordinates. The linear change carries the original spectral measure to a constant multiple of the product spectral measure. With `d` the Haar comparison scalar, `c_j(x, z)` the original coefficient in the new coordinates and `χ_z(a)` the ambient imaginary character on the positive subgroup, the coefficient of the compressed packet is

\[
  d \int c_j(x,z)\left(\int_S \chi_z(a)\,da\right) dz.
\]

The inner integral is continuous in `z` by dominated convergence, since the character has absolute value one. The outer integral is smooth in `x` by differentiation under compact integration and is supported in the projection of the original compact support. The compressed packet retains the inducing vectors, continuations and holomorphy domain of the full packet.

On quotient representatives, the ambient shift gives the factor `χ_z(a)` times the value at the relative parameter. The norm-one representative contributes trivial ambient character. Rational invariance of the continuations makes the full value independent of its rational representative. For the relative continuation, split-centre covariance has factor one because the relative parameter annihilates the centre's logarithm. Thus the relative value may be evaluated at `y.out`. At each fixed `y`, scalar holomorphy gives continuity of these values in the spectral coordinates. The compact coefficient supports and the finite measure of `S` give the integrability needed for the spectral and central Fubini interchanges. They identify the evaluation of the compressed relative packet with the central integral of the full packet.

Each full packet used by the standard completeness premise therefore pairs to zero with the lift of `f`. The pairing equals the one with its compressed packet, which meets the target's `MemLp` requirement by the central integral bound. The full completeness premise gives almost-everywhere vanishing of the lift. Applying Fubini on `S × [G]` and using the positive measure of `S` gives `f = 0` almost everywhere on `[G]`.

## Provenance

Delorme, *On the spectral theorem of Langlands* (2023), Theorem 6.1 and Lemma 6.2, p. 22, use the full packets of standard parabolics in the isometric image. Theorem 7.9, pp. 33–35, gives surjectivity on the rational quotient. Its proof on p. 35 splits the relative and ambient spectral parameters and uses Fourier analysis in the ambient direction. Proposition 5.4 on p. 20 gives the decay used to deduce square integrability. The Lean proof uses the split parameters to average full packets against a central indicator. [Delorme 2023](https://doi.org/10.1016/j.aim.2023.109107)

Getz–Hahn, *An introduction to automorphic representations* (2024), §2.6, Lemma 2.6.2 and (2.19)–(2.22), pp. 68–69 (PDF pp. 85–86), give the split-centre and norm-one quotient descriptions. Section 10.5, (10.21)–(10.24) and Theorem 10.5.1, pp. 281–282 (PDF pp. 293–294), uses relative parameters and `[G]`. The conclusion of the Lean implication is the density statement in this normalization, with the exact packet and presentation hypotheses of `RelativeWavePacketCompletenessStatement`. [Getz–Hahn 2024](https://doi.org/10.1007/978-3-031-41153-3)
