# Matrices of homogeneous polynomial substitution

Let `R` be a commutative ring and `σ` a type of variables. This is an internal
construction from Mathlib's homogeneous polynomial submodules, bases restricted
to specified monomial supports, and the matrix of a linear map in a basis.
It supplies the polynomial calculation needed for comparing determinants of
actual augmentation layers. There is no additional external source claim.

`MonomialIndex σ d` is the type of finitely supported natural exponent vectors
of total degree `d`. For finite `σ` this type is finite, including when `σ` is
empty. The coefficient ring and variable type have independent universes.
`monomialBasis σ d R` is the basis of the degree-`d` homogeneous submodule
indexed by these vectors. Its vector at `e` is the actual monomial `X^e`
with coefficient one, and its coordinate at `e` is the actual polynomial
coefficient. The implementation transports Mathlib's support-restricted basis
across the equality with the homogeneous submodule.

For a finite variable type, `column M j` is the homogeneous linear polynomial
`∑ i, M(i,j) X_i`. The map `action M d` substitutes these linear polynomials
in each homogeneous degree-`d` polynomial. The identity matrix acts as the
identity, and `action (M*N) d = action M d ∘ action N d`, with the column
convention specified by this formula. These facts follow from evaluation of
the column polynomials and composition of polynomial evaluation.

`representation M d` is the matrix of this action in `monomialBasis`.
`representation_apply` identifies an entry `(e,f)` with the coefficient of
`X^e` in the substituted monomial `X^f`. `representation_one` and
`representation_mul` prove identity and multiplicativity of this matrix
construction. They use the corresponding action identities and Mathlib's
matrix-of-composition theorem.

For a diagonal matrix with entries `a_i`, `aeval_diagonal_monomial` computes
the substitution of `X^e` as `X^e` times `∏ i, a_i^(e_i)`.
Thus `representation_diagonal` identifies its matrix as diagonal with exactly
those entries. `det_representation_diagonal` states its determinant as the
product of those weights over degree-`d` monomials. This module does not yet
identify that product with a uniform power of the original determinant.

For every ring homomorphism `f : R →+* S`, `representation_map` states that
entrywise application of `f` to `representation M d` gives
`representation (M.map f) d`. The proof first computes coefficient change for
column polynomials and substituted monomials, then takes coefficients. There
is no injectivity, field or domain hypothesis on `f`. This is coefficient-ring
naturality of the explicit matrix, without a sheaf base-change assertion.
