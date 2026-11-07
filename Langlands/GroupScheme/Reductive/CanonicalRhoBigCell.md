# Canonical rho geometric data

This internal construction combines the canonical polarized-rho dynamics,
the rational opposition representative, the extremal diagonal coefficient,
and the all-test unit-cell theorem. It provides the first six laws of the
existing `SteinbergBigCellStatement` from explicitly supplied structural
and representation data.

`SteinbergBigCellGeometricData` records the same witnesses as the complete
`SteinbergBigCellData`, together with left covariance, inverse right
covariance for the same coordinate, value one at the identity, the
nonzerodivisor property, global factorization wherever the coordinate has
unit value, and a diagonalizable lift for every common point of the two
subgroup maps. Every test scheme is relative to the original field; neither
affineness nor reducedness of test schemes is imposed.
`withIrreduciblePowers` appends the exact remaining law about cofinal finite
bases and irreducibility of the entire covariant spaces, preserving all
witnesses and coordinates.

The auxiliary restriction theorem identifies a minimum-weight character
from the actual diagonal entry on the supplied torus. The evaluation formula
for the minimum-weight character, followed by the torus factorization into
the parabolic, identifies its evaluations on every test. Extensionality
of rational characters then proves the character-lattice equality. Thus
the final construction needs the diagonal entry's torus weight rather than
an assumed identity for a character of the parabolic.

The general helper `Dynamic.extremalNegativeRhoBigCellGeometricData`
assembles these six laws for a supplied cocharacter, represented parabolic
and centralizer, closed parabolic embedding, rational opposition point
and its two required reversal laws, extremal representation, and Bruhat
covering. It uses the supplied root datum on the original split maximal
torus and the same extended negative-rho coordinate throughout.
The canonical specialization below constructs the parabolic, centralizer
certificate and opposition point needed by this helper.

For `canonicalRhoBigCellGeometricData`, supply a connected reductive affine
group over an algebraically closed field, its split maximal torus, and a
finite reduced root datum on that same torus with `IsRootDatumOf`, a base,
and full integral coroot span. Also supply an actual finite matrix
representation in coordinates diagonalizing the polarized-rho cocharacter,
a unique smallest-weight coordinate whose torus diagonal entry has weight
negative rho on every test, and `BorelTorusBruhatCovering` for the canonical
dynamic parabolic and the original torus.

The subgroup is the affine dynamic parabolic of polarized rho; its closed
immersion and representation of the orbit-extension functor are constructed.
The canonical rho centralizer theorem makes the original torus its
represented centralizer. The rational opposition representative is
constructed from the supplied root datum, and its proved negation laws give
both the opposite parabolic and the required action on negative rho.
The weight coordinate is the extended negative-rho coordinate on this
parabolic, and the group coordinate is the distinguished diagonal matrix
coefficient of the original representation.

The extremal-coefficient theorems prove left and inverse right covariance
for this same weight coordinate. The diagonal entry equals one at the
identity; the connected reductive coordinate-domain result makes it a
nonzerodivisor. The extremal unit-cell theorem and supplied Bruhat covering
produce the global opposite-parabolic factors on the original test scheme.
The intersection of opposite dynamic parabolics is the represented
centralizer. A diagonalizable presentation of the original split torus
therefore supplies the final intersection lift, without changing its
subgroup functor.

This is an internal derivation from the imported canonical-rho,
opposition, extremal-coefficient, unit-cell and diagonalizable-torus
constructions; it does not claim a new literature transcription.
The file does not establish structural existence, the extremal
representation or its weight properties, or the Bruhat covering. It does
not prove finite-dimensionality or irreducibility of entire covariant
spaces. The exact host proposition remains a separate proof obligation.
