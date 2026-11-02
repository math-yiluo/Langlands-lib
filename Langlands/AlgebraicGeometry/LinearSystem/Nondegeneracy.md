# Nondegeneracy of a complete linear system on a reduced scheme

`basisHyperplaneSectionEquiv` matches actual homogeneous linear polynomials
with actual global sections having the same coefficients in a specified
finite ordered basis of the full section module over the coefficient ring.
It is the composition of the coordinate equivalence for the degree-one
polynomial basis with the inverse coordinate equivalence for the section
basis. Its value is the existing scalar combination `linComb`.

The nondegeneracy theorem assumes that the source scheme is reduced and that
the section basis generates at every scheme point. It proves that, for every
nonzero homogeneous linear polynomial, some image point of the actual
`linearSystemMap` has homogeneous prime ideal not containing that polynomial.
No embedding or field hypothesis is required.

The proof uses the existing result that a line-bundle section with empty
trivialization open on a reduced scheme is zero. A nonzero combination thus
generates at some point. On a generating-section chart through its residue
field point, its ratio is nonzero. Reducedness of that field spectrum makes
the basic open of this nonzero ratio nonempty. The chart preimage formula
identifies this with the corresponding projective hyperplane complement.
For a full section basis, the coefficient equivalence carries a nonzero
polynomial to a nonzero section, and the degree-one basis expansion identifies
the polynomial with the one in that argument.

This is an internal consequence of the published section-zero test,
linear-system charts and degree-one coordinate basis. It uses no new
external source assertion. Existence of the finite section basis,
generation, reducedness for any particular application, closed immersion and
moduli representability remain separate obligations.
