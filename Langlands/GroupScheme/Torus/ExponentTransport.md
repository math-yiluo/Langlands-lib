# Actual fixed-exponent transport through coordinate torus homomorphisms

Author: Worker 693.

This internal helper translates an all-test character formula into equality of
actual cocharacter maps over an arbitrary base scheme.

`splitTorus.exponentPushforward` is the integer coordinate transpose of a
linear character-lattice map: its coordinate at `j` is the pairing of the
image of the `j`th coordinate character with the original exponent vector.

`groupHom_exponentCocharacter_comp` takes an actual homomorphism between
coordinate split tori and an all-test formula for its character pullback.
It proves that composing any actual fixed-exponent cocharacter with that
homomorphism is the fixed-exponent cocharacter of `exponentPushforward`.
The proof evaluates the supplied formula on coordinate characters, uses the
actual power-map evaluation of the original cocharacter and combines the
powers into their integer dot product. Equality on every test scheme detects
equality of the original group maps. No connectedness, reducedness or
field-valued-point assumption on the base is needed.

`exponentPushforward_eq_coweightMap` identifies the coordinate transpose with
the contravariant coweight map of a full root-datum equivalence, assuming that
both coordinate root-data pairings are the standard integer dot products.
It evaluates the equivalence's pairing-transpose identity on each coordinate
character.

The provenance is an internal deduction from the published fixed-exponent
character/cocharacter constructions, actual torus point equivalences and
the root-datum equivalence laws. No torus homomorphism is constructed from
lattice data by this unit.
