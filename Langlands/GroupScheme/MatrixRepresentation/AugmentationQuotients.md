# Actual augmentation quotient tests and Frobenius

This internal construction uses the existing actual coordinate algebra and
identity augmentation of an affine group scheme over a field, together with
the actual supplied matrix representation. No representation or structural
subgroup is assumed to exist beyond the supplied objects.

`quotientAlgebra G N` is the coordinate algebra modulo the `N`th power of the
identity ideal. `quotientMap` is its canonical algebra homomorphism, and
`quotientPoint` is the genuine affine test point corresponding to that map.
Its point coordinates are exactly the quotient map. Evaluating any supplied
representation at this point reduces its universal matrix entrywise.
No reducedness or finite dimensionality of the quotient is required; `N = 0`
gives the zero algebra and is allowed.

For any exponent characteristic `p` of the field and `N ≤ p^e`,
`quotient_pow_origin` shows that the `p^e`th power of any quotient coordinate
equals that of its scalar constant term. Subtracting the constant term gives
an element of the augmentation ideal. Its `p^e`th power lies in the `N`th
ideal power and therefore vanishes in the quotient. The characteristic-power
ring homomorphism turns this vanishing into the asserted equality.

Consequently `frobeniusPower_affineMatrix_quotientPoint` proves that the
actual Frobenius-powered representation is the identity matrix at this test
point whenever `N ≤ p^e`. The proof uses the existing entrywise Frobenius
formula and the augmentation identity of the universal representation matrix.
The result also covers characteristic exponent one: its condition then
restricts the quotient order to at most one.

These are direct algebraic consequences of the existing affine-coordinate
and Frobenius constructions, with no external literature claims. They do
not assert tensor irreducibility, highest-weight or Steinberg representation
existence, induced-space comparisons, or the Steinberg big-cell statement.
