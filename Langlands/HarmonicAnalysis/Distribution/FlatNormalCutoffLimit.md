# Uniform cutoff limits for flat tests

A distribution on the complement of a zero section has a weighted derivative
bound on a fixed compact support if its values are controlled by the constant
bounding the derivatives in units of a power of the normal distance. Assume that
a family of distributions satisfies one such bound on a parameter set.

For a sufficiently flat test, remove a shrinking normal neighborhood. The
resulting tests are supported inside the punctured domain and in the original
compact set. The difference of two such tests is the difference of the two
near-section cutoffs. The weighted cutoff estimate bounds the two terms by
constants times their inverse scales. This makes the evaluations uniformly
Cauchy in the parameter, and completeness of the complex numbers gives uniform
convergence. The cutoff is eventually the identity on any compact support
that already avoids the section. On an open complex parameter domain the limit
is holomorphic when all punctured evaluations are holomorphic.

`FlatNormalCutoffLimitStatement` records the uniform convergence. This is an
internal local step for extending spectral distributions across a lower Bruhat
cell after flattening the test jets.
