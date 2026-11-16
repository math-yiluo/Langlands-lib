# Unit cell coordinates for actual rank-one reflections

This is an internally derived application of actual relative centralizers,
coordinate-preserving cell base change and the field unit-coordinate theorem.
It makes no new external-source correspondence claim.

`corootBaseChangeCellData` base changes the actual centralizer cell over a
local ring to any commutative algebra. It retains the lifted opposite root
maps and the original exponent character.

`exists_fieldUnitCellCoordinates` chooses a nonzero scalar for the actual
three-factor Weyl product on each supplied field fibre. The product normalizes
the inherited split torus through the prescribed coordinate reflection.
Multiplication on the left by the positive root at one has cell coordinates
whose two scalar entries are units. The proof transports the root datum to
identify the reflection, uses the closed fibrewise maximal torus to put the
square in the torus, and uses connected reductivity and smoothness to obtain
irreducibility. The field unit-coordinate theorem then supplies the entries.

The base ring is an arbitrary commutative local ring; reducedness,
noetherianity, henselianity and characteristic restrictions are not imposed.
The ambient closed fibrewise maximal torus, actual opposite parametrizations
and a cocharacter with exactly the two-root annihilator remain supplied.
The construction of ring Weyl data and the full Isomorphism Theorem remain open.
