# The reflection-generated normalizer for integer-valued building data

This is an internal extension of the published constructions in
`RootReflectionWeyl` and `ReflectionNormalizerWeylAction` to
`IntegerValuationBuildingData v G`, for an arbitrary field `k : Type u`,
an integer-valued valuation `v`, and an affine group scheme `G`. The supplied
datum already includes connected reductivity, a maximal split torus, a
KP apartment and full omega compatibility. No local-field or topological
hypothesis is added.

`reflectionNormalizer` is the closure in the actual normalizer points of
all representatives `p.1 * g * p.2` supplied by opposite factor pairs of
nonidentity relative-root points. Every such representative is a generator.
`reflectionWeylAction` is its actual apartment action restricted to the
affine Weyl group; it is surjective.

The implemented proof of the upper containment uses the actual coroot and
affine reflection action proved in `IntegerRootReflections`. The published
arbitrary-field doubling theorem in `AffineRootDoubling` applies because
actual rank-one factorization supplies all opposite pairs. It makes either
the point functional or twice that functional an ordinary affine root.
Scaling the coroot by the reciprocal scalar leaves its reflection
unchanged, so each generator acts in the affine Weyl group. Closure gives
the upper containment.

For the reverse containment, every ordinary affine root is an extended
root and hence is the point functional of some nonidentity root point.
An opposite pair supplies a representative in `reflectionNormalizer`.
The coroot uniqueness theorem in `IntegerAffineRootArrangement` identifies
its actual coroot with the coroot of the given affine Weyl generator.
Thus every affine Weyl generator, and then its generated subgroup, is
realized. This proves `reflectionNormalizer_map_eq_affineWeylGroup`.

The construction and proofs are derived from the named published Library
modules rather than a new transcription of literature. They include rank
zero. They assert equality for the reflection-generated subgroup only;
identifying the image of the full normalizer remains a separate obligation.
