# Reduction of the derived and central split product to surjectivity

Author: Worker 1482.

This internal auxiliary result uses the full-kernel finiteness theorem in
`CentralSplitTorusProductKernel` and the published general flatness and
finite-kernel quotient results. It makes no additional literature assertion.

`DerivedCentralSplitTorusProductReductionStatement.{u}` retains all the
quantifiers and hypotheses of `DerivedCentralSplitTorusProductStatement.{u}`.
For these data it asserts that the actual multiplication map is a central
isogeny if and only if its underlying scheme map is surjective.
`derivedCentralSplitTorusProductReduction` proves this equivalence. This does
not prove the surjectivity assertion or the original unconditional target.

The forward implication from surjectivity is proved in the stronger pointwise
lemma `isCentralIsogeny_derivedCentralSplitTorusProduct_of_surjective`. This
lemma needs only splitness of all three factors, closedness of the derived and
central inclusions, centrality of the latter and the two displayed
compatibilities. It does not need maximality of either split torus, maximal
centrality, or closedness of the map between the derived and ambient split
tori.

The source product is smooth, affine and of finite type over the field, while
the target split torus is smooth. The published `flat_of_surjective` therefore
gives flatness over an arbitrary field. Affineness of the source implies
quasi-compactness of the multiplication map. The full finite kernel proved in
`CentralSplitTorusProductKernel` then makes the map finite by
`isFinite_of_finite_kernel`, which descends finiteness along the actual fpqc
kernel-pair square. Local finite presentation follows from local finite type
and the Noetherian target. Centrality of the full kernel holds on every test
scheme because the source product is commutative; the proof checks the two
coordinates through `productPointsEquiv`. The reverse implication is the
surjectivity field of `IsCentralIsogeny`.

The arbitrary universe, imperfect fields, positive characteristic and
nonreduced test schemes are retained. No smoothness or reducedness of the
kernel is required.
