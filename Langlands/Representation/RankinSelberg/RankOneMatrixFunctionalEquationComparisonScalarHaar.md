# Scalar additive Haar and natural GL₁ Haar transport

This internal derived prerequisite relates the exact supplied scalar additive
Haar measure to the naturally weighted actual GL₁ Haar measure. It is a
consequence of the published GLAdditive density-cancellation theorems and
Mathlib product-measure equivalences. It asserts no model-vector comparison or
functional equation.

`oneByOneScalarEquiv` evaluates the only entry of a size-one matrix. It is the
composition of the measurable equivalences for the unique row and column.
`oneByOneScalarEquiv_measurePreserving` composes their exact product-measure
preservation statements: the rectangular product of the supplied `ν` maps to
that same `ν`, with no scale change.

For a scalar measure with null singletons,
`rectangularMeasure_one_restrict_invertible` proves that restricting the
size-one rectangular measure to invertible matrices does not change it.
Almost every scalar is nonzero, its size-one determinant is its only entry,
and the determinant criterion gives matrix invertibility. This is only a
size-one null-locus argument; no general determinant-zero theorem is used.

In the canonical p-adic setting, the required null-singleton property follows
from the nontrivial spectral norm: zero has a nontrivial punctured neighborhood
filter, and additive Haar on the locally compact field therefore vanishes on
singletons. The canonical topology is definitionally the spectral norm topology.

`integrable_generalLinear_one_natWeight_iff` transports genuine integrability
of an arbitrary complex scalar function to GL₁ with the natural determinant
weight of exponent one. `integral_generalLinear_one_natWeight` gives the integral
formula. Both apply to every canonical p-adic field and every supplied additive
Haar `ν`; no self-duality or character is needed. The integral is multiplied by
the inverse of the same fixed positive `GLDeterminantDensity.rectangularHaarScalar
F ν 0` from GLAdditive. This scalar depends only on the field and supplied
measure, independently of every integrand.

The `prod_generalLinear_one` variants prove these assertions on the full joint
product with any s-finite auxiliary measure. The proof uses the published joint
GL density cancellation, removal of the same size-one null locus, and the
product of the identity with the scalar measurable equivalence. The
`generalLinear_one_prod` variants put GL₁ first, by exact product-measure swap.
The integral identities follow the usual Bochner convention for arbitrary
functions; the separate integrability equivalences provide actual convergence
whenever an application supplies it.
