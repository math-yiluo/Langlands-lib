# Smooth evaluation and derivatives of multivariate polynomials

This internal helper connects Mathlib's algebraic formal partial derivatives
with its calculus on the finite-dimensional function space `ι → k`, for any
nontrivially normed field `k` and finite index type `ι`.

`polynomialDerivative p x` is the continuous linear map with coefficients
`eval x (pderiv i p)`. Its application, constant, sum, variable and product
identities are proved directly from formal differentiation and finite sums.
Polynomial evaluation is smooth at every order. Its Fréchet derivative is
exactly `polynomialDerivative p x`.

Both calculus proofs use polynomial induction: constants, addition, and
multiplication by a variable. The derivative proof uses the proved product
identity and the usual analytic sum, product and coordinate projection rules.
This is a derived compatibility result from Mathlib's existing formal
polynomial and calculus APIs. It is needed for applying the inverse function
theorem to standard-smooth polynomial presentations.
