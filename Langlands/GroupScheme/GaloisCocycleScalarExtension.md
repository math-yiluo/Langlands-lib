# Galois cocycle coefficients after a change of base field

`GaloisCocycle.scalarExtension` pulls a natural cocycle back to a new base field and refines its pulled-back cover to a field containing compatible images of the old covering field and the new base field. The multiplicative point comparison is the pullback adjunction with restriction of scalars on the test spectrum. It commutes with group-scheme homomorphisms and conjugation by automorphisms of the new coefficient field over the new base.

If the old covering field is normal, the new cocycle values are the old values at the restricted automorphisms, transported to the new coefficient field. This follows from the projection of the field cover and the naturality of the cocycle. A trivialization on the new field cover descends to the full pullback cover by fpqc descent over the new base. This internal comparison is used at the infinite completions in the central correction argument.
