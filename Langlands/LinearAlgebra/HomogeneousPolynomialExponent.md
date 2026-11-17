# The common exponent in homogeneous polynomial determinant weights

Let `σ` be a finite type of variables and let `d` be a natural number. The
monomial index type is the actual type of natural exponent vectors of total
degree `d`, defined in `HomogeneousPolynomialMatrix`.

This is an internal combinatorial continuation of that module, using
Mathlib's reindexing of finitely supported functions and finite sums and
products. It adds no external source claim.

`reindexMonomial e d` permutes the degree-`d` monomials by a permutation `e`
of the variables. `coordinateExponent σ d i` is the natural-number sum of
the exponent of `i` over all degree-`d` monomials. The theorem
`coordinateExponent_eq` proves that this number is independent of `i`,
by reindexing the monomial sum through the swap of two variables.
If `d > 0` and `i : σ`, `coordinateExponent_pos` proves positivity by
bounding the sum below by the exponent of the monomial `X_i^d`.

`exponent σ d` chooses this common number when `σ` is nonempty.
For empty `σ` it is defined to be `d`. This is a convention: all matrices
on the empty variable type have determinant one, so this value is compatible
with the determinant formula. No assertion that it is the usual binomial
coefficient formula in rank zero is made.
`exponent_eq_coordinate` computes it at any given variable.
`exponent_pos` proves it is positive whenever `d > 0`, including with the
specified empty-variable convention.

For a commutative ring `R` and a diagonal matrix with entries `a_i`,
`det_representation_diagonal_coordinate` rewrites the product of monomial
weights as `∏ i, a_i^(coordinateExponent σ d i)`.
`det_representation_diagonal_pow` then proves that the determinant of the
degree-`d` homogeneous substitution is
`det(diagonal a)^(exponent σ d)`.
The implemented proof uses the diagonal weight calculation from
`HomogeneousPolynomialMatrix`, exchanges finite products, and gathers the
powers of each coordinate. The proof includes empty variable types and
arbitrary commutative coefficient rings.
