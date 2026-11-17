# Full coordinate root-data comparison from a local group isomorphism

This internal construction compares two supplied full global coordinate
root data of split fibrewise maximal tori in reductive groups over an
arbitrary scheme base. The groups need only be isomorphic on one actual
field fibre. No compatibility of that isomorphism with the supplied tori
is assumed: the published field comparison theorem supplies equivalence
of the full realized data, and the coordinate realization equivalences
return an equivalence on both entire integral coordinate lattices.

For an étale-local group isomorphism over a nonempty base, choose a point
of a cover member and its residue field. Pull the given actual local
isomorphism to that field, using the canonical direct/iterated pullback
isomorphisms. This supplies the field-fibre comparison and hence a full
coordinate root-data equivalence.

`globalCoordinateRootDatumEquivOfEtaleLocalIso` chooses this equivalence.
Its existence is proved by the preceding lemmas. This does not yet
align Borel positive systems or assert a global group isomorphism. It
requires only nonemptiness once both global data are supplied, so it
applies to the connected-base parent target without extra assumptions.
