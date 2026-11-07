# Binomial pairings of actual rank-one root coefficients

This internal derived unit uses the polynomial matrices of actual additive
group representations, the published actual root-cell relation interface,
and the proved characteristic-p binomial identity. It introduces the scalar
matrix-coefficient polynomial at an original vector and proves its evaluation
and coefficient formulas. It makes no additional claim from external literature.

Over an infinite field, equality of two polynomials whenever `1 + s t` is
nonzero implies their equality everywhere. Multiplication by the nonzero
polynomial `1 + X t` proves equality of the products at all field elements;
polynomial function injectivity and cancellation finish the argument.

Suppose that an actual raising action E, an actual lowering action F, a
functional ell, and a vector v satisfy the scalar rank-one cell identity
`ell(E(s) F(t) v) = (1 + s t)^m` whenever its cell denominator is nonzero.
First fix t and compare coefficients in s. Then compare coefficients in t.
The implemented proof gives
`ell(E_a F_b v) = choose(m,a)` for a=b and zero otherwise, for the actual
divided-power coefficient operators on the original vector space.
Whenever the diagonal binomial coefficient is nonzero, `F_a v` is nonzero.
At m=p^r-1 every coefficient with a<p^r has this property.

The unit also connects this polynomial calculation to actual group schemes.
For a supplied matrix representation, torus map, cocharacter, and two root
maps satisfying `RootCell.RelationOver` over every relative test scheme,
`affineMatrix_cell_relation` proves the corresponding matrix factorization
over every commutative test algebra, including nonreduced algebras. The proof
transports affine additive parameters and the denominator unit to global
sections and applies the original representation to the supplied cell equality.
This result does not require an infinite field.

The scalar bridge takes a vector fixed by the raising root action on field
points, a functional fixed by the lowering root action on field points, the
vector's coroot weight m on field units, and the normalization ell(v)=1.
The matrix factorization gives the scalar identity by applying these four
premises. The final `dividedPower_pairing` and `dividedPower_ne_zero` theorems
compose this bridge with coefficient extraction over an infinite field.
All root maps, the cell relation, and the vector and functional conditions
remain explicit premises; the argument has not constructed them from
highest-weight data.

The unit does not establish the simultaneous nonzero action of the full
unipotent top distribution or a bound for the entire covariant induced space.
Those remain obligations for the host Steinberg big-cell theorem.
