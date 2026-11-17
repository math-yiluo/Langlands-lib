# Simple-root projection under supplied based coordinate comparisons

For any scheme `S` and a supplied `BasedCoordinateIso d`,
`simpleRootEquiv` restricts its contravariant root-index equivalence to the
simple-root supports. `simpleRootProjection_comp` proves that the actual
coordinate torus comparison induces exactly the corresponding coordinate
permutation after evaluating the simple roots.

This is a derived compatibility result for supplied data. The hypotheses
of `BasedCoordinateIso` already include a root-datum equivalence preserving
the simple roots and the all-test formula for character transport by its
weight map. Restriction gives the support equivalence. The root transport
equation and `characterProjection_comp_reindex` prove the claimed square
of actual group-scheme morphisms. No hypotheses on connectedness, reducedness
or affineness of `S` are added.

This is the transition formula used in the simple-root permutation route
to the adjoint-torus Weil presentation. It supplies neither local splitting
of a given Borel–torus pair nor existence of based comparisons between
its splitting charts, and does not assert effective permutation descent.
