# Closed positive adelic images under actual closed immersions

Author: Worker 112.

This internal construction specializes the actual affine point
closed-immersion adapter to full adelic coefficients and restricts it to the
existing intrinsic positive subgroup. The provenance consists of the published
actual point and topology constructions, the generic algebra-point
closed-embedding theorem, and composition of closed embeddings. It asserts no
new literature theorem.

Let `F` be an arbitrary number field. For affine group schemes `G` and `H`
over `F`, a supplied group-scheme homomorphism whose underlying scheme map is a
closed immersion induces a closed embedding on actual adelic points. The proof
supplies the Hausdorff topology of the infinite adele product and finite adele
restricted product, and applies `isClosedEmbedding_affinePointsTarget` to the
actual full adele ring. The map is the existing `AdelicGroupPoints.map`.

For an affine commutative group scheme `T` and affine ambient `G`, suppose
`i : T.toGrp ⟶ G` is an actual closed immersion. The existing intrinsic positive
subgroup is closed in `T(A_F)`. Its inclusion followed by the actual adelic map
of `i` is exactly `positivePointMap`. Composition proves
`isClosedEmbedding_positivePointMap`.

The range of this actual map is the existing `imageSubgroup`, by unpacking
subgroup image membership. Its range is therefore closed in the ambient actual
adelic point topology, as proved by `isClosed_imageSubgroup`.
`closedImageSubgroup` bundles that same subgroup with this proved closedness;
`closedImageSubgroup_toSubgroup` records its unchanged underlying subgroup.

These results require no supplied splitting, finite torus rank, centrality,
reductivity, finite type, or injectivity or finite index of character
restriction. The intrinsic subgroup is defined by positivity of every actual
rational character even when no splitting is supplied. The closed-immersion
hypothesis is retained explicitly. This unit does not construct a greatest
rational split centre for a general number field, prove closedness of the
positive-times-principal rational subgroup, or assert any measure, reduction
or finite-volume theorem.
