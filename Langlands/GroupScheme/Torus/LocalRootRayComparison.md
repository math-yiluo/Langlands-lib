# Root-ray geometry between field fibres over a local ring

This is an internal derived supporting unit. It extends the published
`LocalRootSupportComparison` from actual roots to their divisibility and
positive-ray data, using actual split-torus lattice coordinates. It introduces
no new root-system realization and asserts no reductivity on a special fibre.

`fieldCocharacterEquiv` compares two field split-torus cocharacter lattices
through their common integral exponent coordinates, just as the existing
`fieldCharacterEquiv` does for characters. Their simultaneous action preserves
the actual integer lattice pairing by the finite coordinate-sum formula.
The character equivalence preserves and reflects membership in any positive
integral tail and disjointness of two such tails, since it commutes with
natural-number multiplication and is bijective. Fixed-exponent characters
and cocharacters retain their specified exponent vectors under these comparisons.

For a smooth affine group over a local ring, with a map from a specified split
torus, the actual root-support comparison on any two field fibres gives root
membership in both directions under this character equivalence. Divisibility
within the actual root set is therefore preserved, including all possible
multipliers greater than one. Together with pairing preservation this identifies
the indivisible positive actual roots for corresponding cocharacters.

An exact finite enumeration on one fibre consequently transports to an exact
enumeration on the other with the original index type and order. Disjointness
of the complete positive integral rays through distinct such roots transports
as well. The proofs quantify over both field algebras in the same arbitrary
universe `u`. They require no connectedness, reductivity, maximality or
monomorphy hypothesis on the ambient group or torus map.

The unit supplies only the ray data for a later integral product comparison.
It does not establish an integral product isomorphism or the parahoric-model
target.
