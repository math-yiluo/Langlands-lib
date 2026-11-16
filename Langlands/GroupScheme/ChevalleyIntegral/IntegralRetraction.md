# Integral polynomial retractions for ordered root products

This internal construction extends the coefficient recovery in
`SplitExistence/Retraction` to every commutative ring, with no chosen base field.
It uses the primitivity of the integral root operators recorded in
`ChevalleyData.e_one_map_ne_zero` and the published ring-general matrix entry
formula `xm_mul_opm_apply`.

For a finite integral matrix nonzero modulo every prime, `exists_matrix_bezout`
constructs integral coefficients whose pairing with its entries is one. The
proof takes the gcd of all entries. Any prime dividing its absolute value would
annihilate the matrix modulo that prime, so the absolute value is one. Finite
Bézout and a sign adjustment give the coefficients. This argument also covers
an empty index type: the stated primitivity hypothesis then cannot hold.

`integralRootCoeffs` chooses these coefficients for `e j 1` and replaces them by
zero wherever that matrix has a zero entry. The integral pairing remains one.
`integralRootCoord` is the resulting linear functional on matrices over any
commutative ring. It commutes with every ring homomorphism. If the supporting
entries are those of a scalar multiple of `e j 1`, it recovers that scalar.
In particular it reads the first coefficient of an ordered product of distinct
positive roots sorted by the existing height function.

`integralRetrAux` successively reads a coefficient and cancels its root factor
on the left. Induction on the list proves recovery of every coefficient on the
list and preservation of the supplied accumulator elsewhere. The construction
commutes with every ring homomorphism. For the complete sorted positive-root
list, `integralRetr` therefore recovers all positive-root coefficients, is zero
on the identity, and is natural under change of commutative ring. Its formula
uses only fixed integral coefficients, sums, products, negation and the finite
divided-power exponentials, so it is polynomial in the input matrix entries.

This file establishes matrix formulas and naturality. It does not assert the
existence of an integral reductive group, a scheme immersion, or comparison of
the fibres of a schematic closure; those remain subsequent constructions.
