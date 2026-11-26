# Additive character transport for real ordinary Rankin–Selberg tests

`realOrdinaryGenerationReduction` proves
`RealOrdinaryGenerationReductionStatement`. The hypotheses supply finite
normalized sums at additive scale \(1\) for the positive equal-rank indices and
for adjacent ranks. For rank gaps greater than one, the hypothesis supplies
pointwise normalized coverage at every positive real scale. The conclusion is
`RealOrdinaryNormalizedGenerationStatement` with the original parameter lists,
irreducibility hypotheses and compatible quotient measures. The rank-one
equal-rank case comes from `rankOneOrdinaryNormalizedTests`.

For a nonzero real number \(a\), the leading diagonal in rank \(r+1\) has
entries \(a^{q-i}\) for \(0\le i\le r\le q\). Conjugation multiplies each
simple-root entry by \(a\). Left multiplication by this diagonal transports
coefficient maps by composition. It preserves the compact and Lie
intertwining identities and the smoothness and polynomial height bounds.
Taking the supremum of their ranges proves the corresponding assertion for
`realWhittakerModel`. Invertibility of left multiplication preserves
nonzero models.

In equal rank take \(q=r\). The bottom diagonal entry is one, so the last-row
Schwartz test is unchanged by the quotient substitution. In unequal rank use
the leading block of the larger character diagonal to change variables in
the smaller quotient. The inverse of the trailing block gives the right
correction on the larger Whittaker function. This correction is the identity
in adjacent ranks and is orthogonal at absolute scale one. It therefore
preserves the compact-finite model in both of those cases. At larger gaps,
changing the sign of the scale uses the same orthogonal correction.

The comparison uses `measurePreserving_shiftQuotient` with the pushed-forward
compatible measure data. The determinant contribution is an exponential in
the spectral variable, so it gives a nowhere-zero entire multiplier. At
absolute scale one this multiplier is one. These identities transport
normalized values without division at the zeros of the reciprocal
L-factor. The finite-sum hypotheses give pointwise coverage via
`HasFiniteOrdinaryNormalizationSum.covering`.

The source is H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
Remark 2.2 on pp. 7–8 gives the change of variables in equal rank. The
unequal-rank comparison applies the same substitution to the padded matrix
in (2.4), p. 6. For gaps greater than one and arbitrary positive scales, the
integral comparison is proved on functions with the right correction and
the generation reduction retains the corresponding pointwise coverage
hypothesis.
