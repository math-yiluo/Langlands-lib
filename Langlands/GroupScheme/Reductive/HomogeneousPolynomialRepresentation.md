# Matrix actions on homogeneous polynomials

This internal construction defines a representation of the square matrix monoid
over a commutative semiring on the submodule of multivariate polynomials of each
fixed homogeneous degree. The variable set is any finite type, including the
empty type, and the degree is any natural number.

The image of `X i` under `substitution A` is the linear form
`sum j, C (A j i) * X j`. These column conventions give
`substitution (A * B) = (substitution A).comp (substitution B)`.
The proof checks the equality on the polynomial generators, expands matrix
multiplication and exchanges the two finite sums. Each substituted linear form
is homogeneous of degree one, so Mathlib's homogeneous evaluation lemma proves
preservation of each homogeneous degree. This constructs `homogeneousMap` and
the actual monoid homomorphism `matrixRepresentation`.

For commutative rings, `specialLinearRepresentation` restricts this
representation along the actual special linear group's matrix inclusion.
`eval_substitution` proves that evaluation at a vector `x` equals evaluation of
the original polynomial at `A.transpose *ᵥ x`.

The provenance is an elementary derived construction using the universal
property of multivariate polynomials and finite sums. It assumes no
highest-weight representation or irreducibility theorem. It does not identify
these representations with the induced covariant coordinate space in the
Steinberg big-cell target or establish the higher-rank Steinberg theorem.
