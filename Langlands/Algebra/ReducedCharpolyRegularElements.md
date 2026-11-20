# Regular elements in central simple algebras

An element of a finite-dimensional central simple algebra is regular
here when its reduced characteristic polynomial is separable.
`ReducedCharpolyRegularBasisBoxStatement` assumes a characteristic-zero
field, a finite basis and an infinite subset of the field for each
basis coordinate. It asserts that a vector with coordinates in those
sets is regular. `reducedCharpolyRegularBasisBox` proves the statement.

In a finite Galois matrix chart, the resultant of the generic
characteristic polynomial and its derivative is a polynomial in the
basis coordinates. It is nonzero because the chart contains a
diagonal matrix with distinct entries. The polynomial cannot vanish
on the product of the images of the infinite coordinate sets. The
characteristic polynomial in the chart is the scalar extension of
the reduced characteristic polynomial, so separability descends.

`reducedCharpoly_coeff_zero` identifies the constant coefficient with
the reduced norm multiplied by \((-1)^d\), where \(d\) is the reduced
degree. `reducedCharpoly_smul` computes scalar multiplication by
substituting \(s^{-1}X\) and multiplying by \(s^d\).
`reducedCharpoly_separable_smul` shows that this operation preserves
regularity for any nonzero \(s\). These three identities apply over
any field.

This is an internal approximation lemma derived from the Library's
reduced characteristic polynomial and Mathlib's polynomial resultant.
It supplies regular elements and scalar corrections for the
local reduced-norm argument.
