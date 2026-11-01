# The unit is an actual matrix rational value

`Langlands.GodementJacquet.MatrixUnitValueStatement.{uF,uV}` states that the
constant rational function `1` belongs to both actual matrix rational-value
families of every nonzero smooth complex representation of `GL_(n+1)` over a
canonical p-adic field. This file defines a proposition; it supplies no proof.

The quantifiers retain every prime, every realization `F : PadicField p`, every
natural `n` including `n=0`, and a representation carrier in an independent
universe. The topology and local-field structures are canonical, and the group
has its Borel measurable structure. The only representation assumptions are
smoothness and a nontrivial carrier. There is no admissibility, irreducibility,
Whittaker functional, additive character or Fourier measure premise.

The two value sets are exactly `Padic.matrixRationalValues F σ` and
`Padic.iotaMatrixRationalValues F σ` from `Zeta` and `AnalyticData`. Membership
requires an actual full-square-matrix Schwartz–Bruhat test, an actual element of
the bi-smooth matrix coefficient submodule, convergence on a right half-plane,
and rational continuation of the integral with shift `s+n/2` and variable
`q^(-s)`. The second set transforms the original coefficient by inverse
transpose. Membership is asserted before taking any Laurent span.

This is an internal prerequisite for normalized generator existence. Its
provenance is the compact-open test construction: the published smooth-dual
separation theorem supplies a coefficient nonzero at the identity; a sufficiently
small compact open subgroup fixes its vector and has determinant norm one.
The subgroup image in the full matrix space is compact and open. Scaling its
characteristic function by the reciprocal coefficient value and Haar mass
makes the integral `1` for every complex parameter. The inverse-transpose
pullback gives the second assertion using the published coefficient transport.
The future proof must carry out these constructions. No common denominator,
rationality for arbitrary tests, normalized generator or functional equation is
asserted here.
