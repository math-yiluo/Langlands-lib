# Finite denominators of actual diagonal corrections and leading roots

This internal module defines `finiteDiagonalIdeles` by applying the
finite-coordinate ring projection to every full idele in a diagonal
tuple, including its inverse.

For a supplied standard-compact Iwasawa factorization of the lower
rectangular unipotent, any finite adele scalar `s` which is itself
integral and clears every finite rectangular entry also clears every
diagonal correction and its inverse. The proof maps the factorization
to the actual finite adele ring. Published standard compact membership
puts the entries of the finite compact factor and its inverse in
`integralFiniteAdeles F`. It appends a zero row to the rectangle and
applies the commutative-ring denominator lemma from
`RectangularCorrectionDenominator`.

The second theorem combines the correction denominator with the
recovered original block-root formula. If `q` clears every actual
corrected simple-root coordinate and `s` clears the correction tuple
in both directions, `q*s²` clears every original leading block root.
The proof uses the correction ratio denominator in reverse index
order and multiplies two known integral finite adeles.

All denominators are common across the tuple and all finite places.
No nonvanishing assumption is needed for these algebraic membership
implications; the construction of a Schwartz majorant will separately
require its final field denominator to be nonzero. These results do
not assert archimedean rapid decay or Mellin convergence.
