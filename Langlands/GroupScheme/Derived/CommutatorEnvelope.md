# The derived subgroup as a closed commutator-image envelope

This is an internal comparison of the published `Derived.Basic` and
`ImageGeneration` constructions. It is valid over any base scheme in the same
arbitrary universe and uses actual morphisms on all test schemes.

`SubgroupFunctor.containsCommutators_iff_containsImage` evaluates the actual
`commutatorMap (𝟙 G) (𝟙 G)` on product points. In one direction its two projections
give the two input points; in the other, the categorical product lift gives a
point whose image is the specified commutator. The published all-test
commutator formula proves both implications. Combining this with the existing
image-containment/factorization equivalence gives
`containsCommutators_iff_factorsThrough`.

The defining intersections therefore have precisely the same closed subgroup
competitors. Pointwise subgroup extensionality proves
`derivedSubgroup_eq_closedImageEnvelope`, including on nonreduced and nonaffine
test schemes. No assertion about rational-point commutator generation enters
this comparison.

`IsDerivedSubgroup.generatedImage` packages an arbitrary exhibiting inclusion
as a representative of that envelope, retaining its original group and
inclusion. Conversely, `GeneratedImage.isDerivedSubgroup` proves that every
representative of this envelope exhibits the derived subgroup. The existing
uniqueness isomorphism of representatives then supplies an isomorphism of the
underlying schemes over the original base. Composing a smooth structure
morphism with this isomorphism proves
`IsDerivedSubgroup.smooth_of_generatedImage`.

These are deductions from the two Library definitions, rather than an appeal
to a structural theorem in the literature. They do not prove the existence or
smoothness of a commutator-envelope representative. In particular, geometric
smoothness over arbitrary fields, including for disconnected groups, remains
a separate proof obligation of `DerivedSubgroupSmoothnessStatement`.
