# Reflection of étaleness under analytification of algebraic spaces

`isEtaleMorphism_of_etale` proves the reflection direction of
`SpaceAnalytificationEtaleStatement` in every universe. The proof tests the
composite with each finite-type étale affine point of the source. Coordinate
rings of its pullbacks against affine étale target charts provide the affine
algebra maps to which the comparison applies. The original-chart transport
and the published affine comparison reflect their localized étaleness.
The analytic projections are étale by the published finite affinoid algebra
descent and the finite-pieces to all-pieces upgrade for localized pullbacks.
The algebraic affine tests then imply étaleness of the supplied morphism.
Source separatedness is unnecessary for this direction.

`spaceAnalytificationEtaleStatement_of_sourceDescent` combines this direction
with the conditional preservation theorem. The remaining hypothesis requires
étaleness to descend along a jointly surjective étale family in the
localized category. Preservation applies that hypothesis to the maps attached
to all étale affine test points of the source. The import of the exact
comparison and its quantifiers are unchanged.

These are internal consequences of the published algebraic affine tests and
conditional analytification reductions, together with the companion affine
chart reflection.
