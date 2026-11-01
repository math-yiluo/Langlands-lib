# Compact inverse corner Fourier families

This internal prerequisite constructs actual scalar Schwartz functions from the
published unipotent transform of a full matrix test. For a matrix test `Φ` and
an invertible right translate `h`, its corner function is

`t ↦ ∫_N Φ(u diag(t,1,...,1) h) χ(u) du`.

The matrix may be singular when `t = 0`. The published corner Schwartz theorem,
applied after right translation of the matrix test, proves that this function is
Schwartz for every `h`. Right congruence invariance of `Φ` is uniform in `t`,
so the resulting family of scalar Schwartz functions is locally constant in
`h`, with equality in the actual test space.

For every supplied self-dual scalar Haar measure, scalar Fourier closure and
self-duality give an inverse Fourier test whose plus Fourier integral is the
original corner function. The construction is locally constant in `h`.
Consequently a compact set of right translates gives a finite set of inverse
Fourier tests, and hence one common compact support in the scalar variable.
Joint local constancy follows from local constancy in the parameter and in the
scalar variable.

For any continuous parameter map into the general linear group and any compact
clopen parameter cutoff, these properties yield an actual Schwartz function
of the parameter and scalar together. This establishes joint compact support,
which cannot be inferred from separate compact support alone.

The results are derived from the published actual corner transform,
matrix right translations, congruence invariance, and scalar Fourier closure
and inversion. They retain the original supplied scalar measure and arbitrary
nontrivial additive character. They do not yet construct the source's compact
complex averaging measure or prove the final paired matrix comparison.
