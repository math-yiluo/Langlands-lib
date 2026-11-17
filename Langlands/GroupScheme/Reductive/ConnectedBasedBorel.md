# Bases of coordinate root data presenting prescribed Borels

This internal construction aligns a full coordinate root datum with an actual
Borel containing its supplied split maximal torus. The field argument chooses
a regular cocharacter presenting the Borel, chooses a root-datum base with
the same positive roots, and compares that cocharacter with the canonical sum
of the positive coroots. Their pairings have the same signs, so the published
regular-cocharacter theorem identifies their dynamic parabolics.

The coordinate pairing is proved to be the actual dot product from realization
of the full root datum. Central torus directions are retained throughout.

Over an arbitrary connected scheme, assume a reductive group, a supplied
split fibrewise maximal torus, a finite reduced full coordinate root datum
realized on every actual field-valued fibre, and a supplied relative Borel
containing that torus. `exists_base_of_connected` applies the field calculation
on one residue fibre. The resulting canonical cocharacter factors through the
original Borel, and the connected dynamic-presentation theorem propagates the
equality to the whole base. Closedness and geometrically connected fibres of
the Borel follow from the relative Borel property and ambient reductivity.
No affineness or Picard hypothesis on the base is needed.

`basedBorelOfConnected` chooses the resulting base, retaining the equality
between the original Borel range and the canonical dynamic parabolic as full
subgroup functors on every test scheme. The proof imports the published
`BasedBorelTransport.cocharacter_baseChange` formula through the actual
coordinate-torus comparison.
This is an internal derived construction from published field structure and
the separately constructed connected presentation rigidity; it does not assert
the parent's isomorphism or conjugacy conclusion.
