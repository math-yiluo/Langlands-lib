# Finite coordinates of the special-linear diagonal torus

This internal adapter compares the finite `Fin n` coordinates with the published
special-linear diagonal torus having pivot `Fin.last n`. It retains arbitrary
fields and universes and every `n`, including zero. It does not construct a
pinning or the full special-linear Tits cocycle presentation.

`lastPivotEquiv` sends a lifted finite index `c` to the off-pivot index
`c.castSucc`. `weightCoord_lastPivotEquiv` identifies the published weight of an
entry `x` with the vector whose `c` coordinate is the indicator of
`x = c.castSucc` minus the indicator of `x = Fin.last n`.

`lastPivotTorusIso` is an actual isomorphism of commutative group schemes,
obtained by reindexing the split-torus factors. The character comparison
identifies pullback of each diagonal-entry character with the character
associated to that finite vector. Its difference formula identifies the
pullbacks of the corresponding weight differences.

The proof uses the factor-renaming character formula and the published
integral character coordinate equivalence. The vector calculation distinguishes
the pivot entry from the other entries; the difference formula then uses
additivity of character pullback. All constructions are derived from existing
Library definitions and the reindexing helper, with no external literature
assertion or classification premise.
