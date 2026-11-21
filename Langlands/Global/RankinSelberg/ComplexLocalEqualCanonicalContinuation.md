# Continuation of the canonical equal-rank normalization in the inducing exponents

`ComplexLocalEqualCanonicalContinuationStatement` takes two affine
inducing lines and a row Schwartz function. Its premise is the exact
entire pair normalization for all canonical compact-finite coefficient
pairs on a disk about the initial line parameter. The conclusion is the
same normalization for all canonical compact-finite coefficient pairs at
the target line parameter one.

For each pair of target vectors, the proof transports their compact
restrictions to the initial parameters. The corresponding affine Jacquet
families recover the target vectors at parameter one. Their primal and
dual ordinary integrals are jointly holomorphic on a uniform spectral
right half-plane over the parameter disk of radius three. The angular
weights stay fixed, so the central sign remains fixed and nonzero.

The complex pair parameter reflection theorem then propagates the
entire normalization from the initial disk to parameter one. It uses the
ordinary primal and reflected dual half-planes and the holomorphic
reciprocal Gamma and epsilon factors. Substituting the recovered
endpoint coefficients gives the asserted normalization.

This is an internal continuation step for Jacquet's argument in
*Archimedean Rankin–Selberg integrals* (2009), §8.1, pp. 53–54. The
implemented continuation uses the Library's holomorphic spectral
reflection theorem. The normalized identities on the initial disk are
the explicit premise of this step.
