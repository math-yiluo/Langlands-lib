# Restricting representations to split invariant coordinates

This internal helper works over any commutative base ring. A matrix `B` includes
an `m`-coordinate module in an `n`-coordinate module, and `C` is a supplied
retraction with `C * B = 1`. The Prop-valued predicate `IsStableCoordinates`
requires, for every relative scheme test and every group point, that the ambient
action on `B` equal `B` times its coordinates obtained with `C`.

`coordinateMatrixHom` constructs the matrices `C ρ(x) B`. Stability proves
multiplicativity, and the retraction equation proves the identity law. Since
the domain is a group, these matrices are invertible. Scalar-map naturality
and naturality of the original representation prove compatibility with all
test maps. Group-valued Yoneda, through the published `homOfPoints`, then
constructs the actual `restrictCoordinates` group-scheme representation.

`restrictCoordinates_pointMatrix` identifies its matrices on every test.
`restrictCoordinates_intertwines` restates the supplied stability as the actual
intertwining equation. A vector fixed by this restricted representation maps
to a fixed vector of the original representation. The coordinate inclusion is
injective by its left inverse, so it preserves nonzero vectors.

These are derived matrix and Yoneda constructions using the existing
`MatrixRepresentation`, `IsFixedVector`, `scalarMap_naturality`, and
`homOfPoints` interfaces. They do not assert that a given subspace is stable;
that remains a separate mathematical obligation.
