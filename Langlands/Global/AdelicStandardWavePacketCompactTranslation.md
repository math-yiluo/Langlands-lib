# Infinite compact conjugation of standard-parabolic wave packets

Let `P` be a standard parabolic with `P(𝔸)K = G(𝔸)`. For an infinite adelic point
with image `t` in `G(𝔸)`, set `L = tKt⁻¹`. Right translation sends an inducing
form `φ(g)` for `K` to `φ(gt)` for `L` by
`isSquareIntegrableInducedForm_infiniteRightTranslate`. The Eisenstein series
of the translated form differs from `E(λ,gt)` by the entire height factor
`a^{λ}(q)`, where `q` is the parabolic component of `t⁻¹` in the Iwasawa
decomposition for `L`.

`standardWavePacketCompactTranslation` multiplies the original continuation
`E(λ,gt)` by this factor. Multiplication preserves meromorphicity on the same
domain. The conjugation identity for Eisenstein series gives agreement on the
original regular region. In the given real spectral coordinates `x`, the
factor is `exp(ℓ(x))` for a real-linear complex-valued function `ℓ`. Multiplying
the test coefficient by `exp(-ℓ(x))` preserves smoothness and compact support.
The factors cancel pointwise, so a one-form integral retains its one-form
presentation with the same spectral coordinates and continuation domain.

`IsParabolicWavePacket.infiniteRightTranslate` applies this identity to each
summand and obtains the translated integral by congruence of the integrands.

The construction uses the parameter twist in Bernstein and Lapid, *On the
meromorphic continuation of Eisenstein series* (2024), §2.2, equation (2.1),
and the compact spectral tests in Delorme, *On the spectral theorem of
Langlands* (2023), §5.2 and Lemma 7.11.
