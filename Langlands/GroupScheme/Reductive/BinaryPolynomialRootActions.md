# Root transvections on binary homogeneous polynomials

This internal derived construction uses the actual upper and lower
transvections in `Matrix.SpecialLinearGroup (Fin 2) R` over a commutative ring.
The substitution convention is the column convention of
`HomogeneousPolynomialRepresentation`.

The upper transvection fixes `X 0` and sends `X 1` to `C t * X 0 + X 1`.
Its action on `X 0 ^ a * X 1 ^ b` is the sum over `0 <= r <= b` of
`C (choose b r * t ^ r) * X 0 ^ (a+r) * X 1 ^ (b-r)`.
The lower transvection fixes `X 1` and sends `X 0` to `X 0 + C t * X 1`.
Its action on the same monomial is the sum over `0 <= r <= a` of
`C (choose a r * t ^ r) * X 0 ^ (a-r) * X 1 ^ (b+r)`.
These formulas include zero exponents and arbitrary characteristic.

The proof computes the column forms of the actual two matrices, applies the
binomial theorem, and rearranges factors in the commutative polynomial ring.
The provenance is elementary derived algebra. No basis comparison,
irreducibility, induced-coordinate identification or higher-rank Steinberg
statement is asserted here.
