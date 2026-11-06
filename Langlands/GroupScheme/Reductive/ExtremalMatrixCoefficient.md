# Normalized matrix coefficients from a unique smallest weight

This derived companion to `DynamicExtremalLines` constructs the actual
coordinate `diagonalMatrixCoefficient ρ j` of an affine group over a field.
It is the matrix coefficient of the standard coordinate covector and
vector at `j`. Its value on every relative scheme test is the `(j,j)`
entry of the matrix of `ρ`; at the identity its value is one.

Suppose the restriction of the supplied representation `ρ` to a supplied
cocharacter `ν` is the diagonal cocharacter of weights `e`. Suppose also
that `e j` is strictly smaller than every other coordinate weight and
that `i : H → G` represents its dynamic parabolic. The coefficient lies
in the actual left-covariant coordinate subspace for the rational
character `minimumWeightCharacter` constructed from that coordinate.
The proof applies the all-test covector law to the existing
`EigenMatrixCoefficient` construction.

Inverting `ν` negates `e`. Hence the same coordinate is the unique
maximum for the opposite cocharacter. For a supplied affine
representative `iQ : Q → G` of its parabolic,
`oppositeMaximumWeightCharacter` is its actual eigenvector character.
The action at the inverse point gives inverse-right covariance of the
same coefficient with the negative of this character.

The proofs use the published diagonal-cocharacter inversion identity,
the derived extremal-line action laws, and elementary matrix-coefficient
evaluation. Every pointwise conclusion ranges over all original relative
test schemes, without an affine or reduced restriction.

The representation, diagonalization equality, unique extremal coordinate
and represented subgroups remain supplied data. The two characters have
not yet been identified with one another or with negative rho. No
highest-weight representation existence, nonzerodivisor, big-cell
decomposition or Steinberg irreducibility theorem is claimed here.
