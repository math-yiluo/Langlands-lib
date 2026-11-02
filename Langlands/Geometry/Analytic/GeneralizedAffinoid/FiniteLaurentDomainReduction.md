# Finite pure Laurent reduction of a full affinoid domain

This internal supporting construction iterates the actual independent completed
Gauss Laurent field extensions for a full represented affinoid domain `U` over
an actual presented ambient algebra `A`. The coefficient field stays in its
original universe `u`. No nontriviality, strictness or radical-radius condition
is imposed on the original complete ultrametric field or the two presentations.

`Domain.LaurentReduction` stores a complete pure Laurent field extension, an
actual ambient presentation over that field, and an actual full domain over it.
Both presentation arities and all original radii are retained. It also stores
the continuous map from the original domain locus obtained by composing the
Gauss sections, descent of finite unions of rational neighborhoods at its image
points, and descent of actual finite ambient rational covers. The descended
charts retain genuine bounded restrictions into the original full domain.

`self` uses the original field, algebras and domain, with identity maps.
`adjoin` uses `ScalarExtension.presentation` and `ScalarExtension.fieldDomain`
for an independent positive radius. Their presentation radii are unchanged.
The new section is the composite of the old section with the new field-domain
Gauss section. The neighborhood and cover descent operations compose the
one-step descents with the already stored descents.

`exists_for_radii` inducts on a finite list of positive real radii. It first
treats the tail, then leaves the resulting data unchanged if the head already
belongs to the radical value group. Otherwise its nonmembership gives the
integral-power independence needed for the next completed Laurent field to be
a field. The actual new Laurent variable has the prescribed norm and witnesses
the head radius with exponent one. The isometric Laurent inclusion preserves
all previously obtained scalar witnesses. This constructs the data together
with the tower; it does not eliminate a proposition-valued tower certificate
into a type-valued construction.

`exists_nontrivial_for_radii` includes radius two in that finite family. A
positive power of two realized as a scalar norm is greater than one, so the
resulting field is nontrivially valued. `exists_strictifiable` applies this to
the combined ambient and domain-algebra presentation radii. The preserved
radius identities then give radical-value-group witnesses for every radius of
both resulting actual presentations.

The provenance is internal composition of the published pure Laurent radius
extension, full Laurent field-domain construction, Gauss sections and
finite-union rational-neighborhood descent. This unit constructs a common
field with simultaneous radius witnesses and all required descent operations.
It does not prove strict local Gerritzen–Grauert or the host finite rational
cover statement. Arbitrary closed ideals, zero and nonreduced quotients, empty
coordinate tuples and empty domain loci remain allowed.
