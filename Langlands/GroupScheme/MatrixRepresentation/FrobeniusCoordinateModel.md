# Exact Frobenius-origin quotient tests of actual affine groups

Let `G` be an actual affine group scheme over a field `k` of exponential
characteristic `p`, and let `r` be a height. This derived unit forms the
image of the actual identity augmentation ideal under the coordinate
ring's `p^r` power endomorphism. `quotientAlgebra G p r` is the quotient
coordinate algebra by this ideal, `quotientMap` is its algebra map, and
`quotientPoint` is the genuine affine point of the original `G` represented
by that map.

Every coordinate `a` in this quotient satisfies
`a^(p^r) = a(1)^(p^r)`, with the identity value mapped into the quotient.
Indeed, `a - a(1)` lies in the original augmentation ideal, so its
characteristic power lies in the image ideal and vanishes in the quotient.
The characteristic-power ring homomorphism converts this into the
displayed equality. For every finite matrix representation of `G`,
the matrix at the quotient point is the reduction of its original
universal matrix. Applying the representation's Frobenius power makes
this matrix the identity. These assertions need neither polynomial
coordinates nor reducedness.

Now supply an actual algebra equivalence from the coordinate algebra of
`G` to a polynomial algebra in `d` variables, with constant coefficient
equal to the original identity evaluation. `map_augmentationIdeal` proves
that this equivalence identifies the actual augmentation ideal with the
polynomial origin ideal. Algebra equivalences commute with characteristic
powers, so `map_quotientIdeal` and the proved polynomial Frobenius ideal
comparison identify the actual quotient ideal with the box ideal at
bounds `p^r - 1`.

`polynomialModelEquiv` is the resulting algebra equivalence from the
actual quotient algebra to the explicit polynomial box. This gives
finite dimensionality and dimension `(p^r)^d`, including height zero and
zero coordinates. The supplied coordinate equivalence is an algebra
equivalence, without any assertion that the group law is coordinatewise
addition.

The proof reuses the published actual point-coordinate and universal
matrix interfaces and follows the augmentation-quotient power argument,
with the exact Frobenius image ideal replacing a power of the ordinary
augmentation ideal. There is no external source assertion. Polynomial
coordinates and their identity compatibility are explicit inputs, whose
existence is not proved here. No Frobenius-kernel group object, root
coordinates, entire induced-space comparison or Steinberg irreducibility
is constructed.
