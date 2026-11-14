# Conjugation on matrix and inverse-matrix coordinates

Author: Worker 631.

This internal construction bundles the published coordinate-conjugation formulas
from `GeneralLinearAffineCoordinates` into an actual homomorphism of group schemes.
It is derived from that module and the Library's natural-point construction
`homOfPoints`; it makes no independent claim from the literature.

For any finite type `n : Type` and any commutative base ring `R` in arbitrary
universe `u`, `GeneralLinear.coordinateConjugationHom n R` maps `GL_n` into
`GL_(Coordinate n)`. The vector space of coordinates is the direct sum of two
matrix spaces. An invertible matrix `U` acts on each summand by `M ↦ U M U⁻¹`.
The second summand represents inverse-matrix entries when the vector is the
coordinate-value vector of an invertible matrix.

`conjCoordsMatrixHom` takes the standard-basis matrix of the published linear
map `conjCoordsLinear U`. Its homomorphism laws follow from `conjCoords_one`,
`conjCoords_mul` and the matrix formula for composition of linear maps.
`conjCoordsHom` lifts this matrix homomorphism to units, using that its source
is a group. `conjCoordsHom_mulVec` identifies its action on every vector;
`conjCoordsHom_mulVec_values` identifies the action on coordinate values with
conjugation of invertible matrices.

`conjCoordsHom_map` proves naturality for ring homomorphisms whose source and
target may lie in independent universes. Matrix entries are evaluations on the
standard basis, whose vectors commute with ring maps; the result then follows
from `conjCoords_map`.

`coordinateConjugationPoints` transports this natural homomorphism through the
Library's general-linear point equivalences. Its naturality under arbitrary
maps of test schemes gives `coordinateConjugationHom` via `homOfPoints`.
The lemmas `pointsEquiv_coordinateConjugationHom` and
`affinePointsEquiv_coordinateConjugationHom` give its matrices over global
sections and over affine test algebras, respectively.
`pointsEquiv_coordinateConjugationHom_mulVec` states on every test scheme that
this matrix takes the values of `y` to the values of `x*y*x⁻¹`.

This supplies the ambient representation for a normalizer argument. Restriction
to a subgroup's coordinate span, identification of its kernel and boundedness
of the induced action remain separate obligations.
