# Weighted Borel averaging of complex matrix tests

Let \(B\) be the upper triangular subgroup of \(\mathrm{GL}_n(\mathbb C)\).
The average of a smooth complex matrix test with compact topological
support in the invertible matrices, weighted by \(c:B\to\mathbb C\), is
\[
  x\longmapsto \int_B c(b)\,\phi(xb)\,d\mu(b).
\]
For a continuous weight, the integral converges absolutely at invertible
arguments and defines a smooth function there. The measure is finite on
compact sets for the second-countable Borel topology of the subgroup.

The proof uses the fact that the parameter taking \(x\) to \(y=x b\)
is \(x^{-1}y\). On compact sets of invertible \(x,y\) the possible parameters
lie in a compact subset of the full group. Its intersection with the
closed upper triangular subgroup gives compact transport. This proves
integrability. For smoothness, multiply the integrand by a smooth matrix
bump equal to one near the invertible argument under consideration.
The same compact transport bounds the parameter support of the resulting
family. The jointly smooth matrix formula gives continuous spatial
derivatives in the parameter, and compact-family integration applies.

If the weight is multiplicative and the measure is left invariant,
evaluating the average at \(g^{-1}\) gives an inducing covariance law.
Replacing \(g\) by \(b_0g\) multiplies the value by \(c(b_0)\) by left
translation in the integral. This is an internal construction for lifting
smooth complex standard-module Whittaker functionals to matrix tests.
