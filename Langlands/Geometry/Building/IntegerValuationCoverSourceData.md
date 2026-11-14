# Source building for an integer-valued derived cover

This internal construction adapts `DerivedCoverSourceData` from local fields
to an explicit integer-valued valuation on an arbitrary field. Unlike that
conditional wrapper, it uses published structural proofs directly.

`CentralizerDatum.ofMaximalSplitTorus` chooses the actual represented closed
centralizer, factors the split torus through it, and uses
`Cartan.restrictionEvaluation_bijective_of_torusCentralizer`. This result has
arbitrary-field scope, so no local-field instance or comparison target is needed.

`DerivedCoverSourceData` bundles a source building on the actual cover, the
forward normalizer homomorphism, the affine apartment equivalence, exact
transport of affine roots, equivariance, and actual lifts for the normalizer
intersection with the simply connected image. Its constructor chooses the
derived and covering split tori using `simplyConnectedDerivedCoverSplitTorus`,
then a central split component and the central-complement isogeny using
`splitComponentStatement` and `derivedCentralSplitTorusProduct`. It chooses
actual centralizer data by the preceding constructor and assembles the
comparison identities from `IntegerValuationCoverBuildingComparison`.

The resulting source building includes the full V6 condition. No normalizer
image equality or other unproved proposition is assumed or proved here. The
source group and maps are those of the supplied derived cover.
