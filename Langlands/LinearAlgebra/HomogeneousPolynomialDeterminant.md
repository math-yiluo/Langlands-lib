# The determinant character of homogeneous polynomial substitution

Let `R` be any commutative ring and let `σ` be any finite type, in independent
universes. The matrix `representation M d` from
`HomogeneousPolynomialMatrix` represents degree-`d` homogeneous polynomial
substitution by the columns of a square matrix `M`.

`determinantCharacter d` is the multiplicative map from the full square-matrix
monoid to the multiplicative monoid of `R` that sends `M` to
`det(representation M d)`. Its identity and multiplication laws follow
from the corresponding laws for `representation` and the determinant.
This includes singular matrices; the definition does not require units.

The theorem `det_representation` proves, with no additional hypotheses,

`det(representation M d) = det(M)^(exponent σ d)`.

`determinantCharacter_eq` states the same formula for the defined character.
The exponent is the common sum of any chosen variable's exponent over all
degree-`d` monomials when there is a variable, and is defined to be `d` for
the empty variable type. The supporting theorem `exponent_pos` proves
positivity in positive degree. These supporting definitions and conventions
are documented in `HomogeneousPolynomialExponent`.

The implemented arbitrary-ring proof uses the universal matrix whose
entries are the independent variables of `B = ℤ[X_(i,j)]`. This polynomial
ring is an integral domain. Mapping it into its fraction field is injective.
The field formula from `HomogeneousPolynomialTransvection`, together with
`representation_map`, therefore gives the identity already in `B`.
The homomorphism evaluating each universal entry at the corresponding entry
of `M` specializes that identity to `R`. Naturality of `representation` and
of determinants identifies both sides with the asserted expressions.
The specializing homomorphism need not be injective. In particular, the
result includes rings with zero divisors and the trivial ring.

The three determinant modules form an internal derivation from the
Mathlib-based substitution matrix, finite monomial permutation symmetry,
elementary matrix generation over fields, and the fraction field of a
polynomial domain. There is no external source claim and no assertion here
about sheaf gluing, the actual group Lie module or ampleness.
