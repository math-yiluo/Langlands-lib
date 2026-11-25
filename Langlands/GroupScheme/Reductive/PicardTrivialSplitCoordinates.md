# Split coordinates over a connected affine base with trivial Picard group

This internal assembly combines full root-datum constancy on a connected
affine base with freeness of actual root-weight modules from triviality of
all actual scheme line bundles.

`hasSplitMaximalTorusCoordinates_of_connected_of_lineBundlesTrivial`
proves that the supplied closed split fibrewise maximal torus has global
split coordinates: take the identity coordinate isomorphism, the single
finite reduced full fibrewise root datum, and the trivializations of all
its actual root-weight modules. The base is the original `Spec R`.

`hasSplitBorelVectorSeries_of_connected_of_lineBundlesTrivial` applies
the published split Borel vector-series theorem to the same data. The
conclusion is the actual existential Borel subgroup containing the supplied
torus, with a split projection onto that torus and an affine kernel carrying
a finite vector-quotient series.

These results are affine prerequisites for the isomorphism and
`G(S)`-conjugacy of reductive groups with split maximal tori and Borel
subgroups over a connected base with trivial Picard group. They do not assert
an isomorphism between two reductive groups or a general-base global
splitting result. No extra module-Picard, representation or local-ring
hypothesis is introduced.

`picardSplitBorel` is the concrete chosen-data construction supplied by these
existence lemmas. It uses classical choice on the proved existence result;
the preceding lemmas state and prove its mathematical existence and scope.
