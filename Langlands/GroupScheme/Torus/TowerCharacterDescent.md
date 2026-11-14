# Signed weight fibers through two character descents

The derived internal construction `characterLattice.descendRestrictFamilyTower` applies the actual split-torus character-lattice
inverse twice. A family on the scalar extension of a split torus `T` is first
descended to `T`, then restricted along a supplied morphism from the first
scalar extension of another split torus `S`, and finally descended to `S`.
Its signed weight fibers at a cocharacter of `S` have the same cardinalities as
the original family evaluated at the cocharacter obtained by the actual two
base changes and the supplied morphism.

The implementation constructs the identity equivalence on the signed index
subtypes and rewrites their predicates with `latticePairing_descendFamily`,
`latticePairing_restrict_descendFamily`, and linearity in the character. It
asserts no family existence, torus morphism existence, or field closure result.
The bases may be any integral domains in the same universe.
