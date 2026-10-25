# A central element detecting the spectral parameter

For a specified p-adic field and topological data `T`,
`centralSpectralElement T m` is the actual rank `m` scalar matrix with diagonal
entry the inverse of the specified uniformizer. Its membership in the monoid
center follows from the existing scalar-to-center homomorphism.

The normalized absolute value of the inverse uniformizer is the residue
cardinality `q`. This follows from the published formula for integral powers of
the chosen uniformizer, specialized to exponent minus one. The determinant of a
rank `m` scalar matrix is the `m`-th power of its scalar, so its normalized
determinant absolute value is `q^m`.

Consequently `determinantWeight` at this matrix and exponent `-s` equals
`spectralPoint q s ^ m`. The proof first computes the real determinant absolute
value, then uses complex-power identities for a natural-number base. These
identities account for the complex logarithm branch; no unrestricted identity
for powers of arbitrary complex numbers is assumed. The result holds for every
complex `s` and every natural rank `m`, including zero.

This is an internal normalization calculation from the existing definitions of
the uniformizer, scalar matrix, normalized absolute value, determinant weight
and spectral point. It is intended for the residual bilinear term in the
equal-rank trilinear reduction. It does not assert integrality of a representation
operator, finite spectral support of bilinear forms, or trilinear uniqueness.
