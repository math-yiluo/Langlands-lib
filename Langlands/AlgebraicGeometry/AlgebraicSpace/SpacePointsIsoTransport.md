# Fibre predicates under isomorphisms of morphisms

This internal comparison unit uses the point homeomorphism
`Points.isoHomeomorph` from `PointTopologyIso`. Its forward map is the point
map of the presheaf isomorphism and its inverse is the inverse point map,
for the existing intrinsic point topologies.

`Points.isClosedMap_of_iso` transports closedness of a point map through
an isomorphism of its source: the new map is the old closed map composed
with the inverse point homeomorphism. The target presheaf and its topology
stay fixed.

`fibrePullbackIsoOfArrowIso` compares the actual pullbacks of isomorphic arrows,
when the map from the common test presheaf is transported with the inverse
target isomorphism. Its projection to that test presheaf is unchanged. The
comparison uses the canonical pullback map on the source isomorphism,
the identity of the test presheaf and the target isomorphism.

The induced point homeomorphism proves that the existing
`HasGeometricallyConnectedFibres` predicate is invariant under an isomorphism
of arrows of algebraic spaces. The same fibre comparison proves invariance
of quasi-compactness by transporting its compact étale atlas, and universal
closedness by transporting its closed point map along this homeomorphism.

These are derived comparisons using the imported definitions and categorical
pullbacks. No literature input, change of base scheme or limit-descent claim
is used in this unit. The point-homeomorphism construction itself is reused
from the separate `PointTopologyIso` module.
