# Actual finite free bundles on disjoint open covers

This internal prerequisite for the relative radical filtration constructs one
actual module sheaf from finite free pieces on a disjoint scheme open cover.
The rank is a separate natural number for each piece; it may be zero, and no
constant rank or nonempty-cover hypothesis is imposed.

`DisjointFreeBundle.module` uses the actual module-sheaf gluing construction.
Its overlap maps are the canonical diagonal identifications and the unique
module identifications on empty distinct overlaps.
`pieceIso` identifies the actual pullback with each prescribed free sheaf.
`frames` transports each free restriction through the open immersion's
isomorphism onto its open image, and then to the corresponding slice site.
These frames cover the base and yield `isFiniteLocallyFree`.

The construction is derived from the Library's module gluing and finite-frame
interfaces. It supplies the module on the disjoint affine chart cover used in
the filtration descent. It does not construct the later descent cocycle, identify
group points with its sections, or assert that a global quotient is a vector
bundle.

`frames` transports each chart to its open image with `DerivedSections.freeChartOnOpensRange`.
