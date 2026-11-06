# Identifying extremal characters with extended negative rho

This internal companion compares the characters constructed from a
supplied diagonalized matrix representation with a unique smallest
coordinate. It retains the represented dynamic parabolic, its supplied
commutative centralizer and the closedness of the parabolic inclusion.

The minimum character and the opposite maximum character both restrict
to the same diagonal-entry character on every common subgroup.
Their evaluations are the same diagonal entry, and pointwise
extensionality on every relative test scheme proves equality of the
actual rational characters.

For a supplied torus factor, conjugation by a normalizing point replaces
that factor by precomposition with the inverse normalizing
automorphism. This preserves injectivity of character restriction.
The dynamic parabolic character equivalence supplies injectivity for
the centralizer factor. If the normalizing automorphism negates the
restricted minimum character, restriction along the conjugate factor
therefore identifies the opposite maximum character with the negative
of the minimum character on the same group `H`.

Now supply a root datum `P`, a base, full integral coroot span, and the
equality of the restricted minimum character with negative rho.
The previously proved uniqueness criterion identifies the minimum
character with `negativeRhoCharacter`. If the supplied normalizing
automorphism sends negative rho to rho, the opposite maximum character
is the negative of that same extended negative-rho character.
Consequently the normalized diagonal coefficient has both left
covariance and inverse-right covariance for precisely
`negativeRhoCoordinate`, on all original relative scheme tests.
The definition `negativeRhoDiagonalCoefficient` packages that diagonal
coefficient as an element of the actual negative-rho left-covariant
function space; its underlying coordinate is the previously normalized
`diagonalMatrixCoefficient`.

The proof is derived from the actual character restriction equivalence,
the extremal diagonal-entry evaluation formulas, the normalizing
automorphism, and negative-rho uniqueness. No external theorem is
invoked here.

The representation, diagonalization, unique coordinate, structural
subgroups, root datum, prescribed restricted weight and normalizing
point remain supplied data. In particular, this file constructs no
highest-weight representation and does not prove its existence,
nonzerodivisor properties, a big-cell decomposition or Steinberg
irreducibility.
