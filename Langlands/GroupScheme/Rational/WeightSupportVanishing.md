# Trivial subgroups and vanishing ambient weight support

This internal helper uses the actual all-test subgroup functor and tangent
image. The unit from the trivial group scheme represents the identity
subgroup on every test. For a separated group scheme it is a closed
immersion: its composite with the structure map is the identity of the
base. Over a field its source is the base scheme, which is smooth over
itself and connected. Every automorphic action fixes the identity
subgroup. Its tangent image is the zero submodule, by injectivity of the
subtype map from the actual identity kernel.

`HasNoAmbientWeights b A` says that every character of `A` is absent from
`actionWeightSupport b ⊤`. The empty semigroup has zero weight span.
Assuming the exact `SemigroupRealizationStatement`, its uniqueness clause
therefore identifies the empty-semigroup subgroup with the identity
subgroup. A semigroup with no ambient weights has zero weight span:
any nonzero vector in one of its summands would witness an ambient
weight in that semigroup. The implementation reuses
`actionWeightSpace_eq_bot_of_not_mem_support` from `SemigroupPartition`
for this step. The same uniqueness clause then identifies
its subgroup with the identity subgroup. Specializing this argument
to a positive cyclic tail proves the stated tail-vanishing lemma.

The published `actionWeightSpace_conjugation` from
`ActionWeightComparisonProof` identifies the intrinsic conjugation weight
space with the original adjoint weight space. A nonzero character is
therefore an ambient conjugation weight precisely when it is in
`relativeRoots i`: in either direction a nonzero vector witnesses the
corresponding nonzero submodule. No assertion that zero occurs is made.
For a split torus, positive multiples of a nonzero character are nonzero;
this is the imported `IsSplitTorus.nsmul_ne_zero` from
`WeightVectorUniqueness`. Hence a cyclic tail containing no relative root
has no ambient weights, and the preceding conditional vanishing theorem
applies. If the double character is not a root and no multiple with
coefficient at least three is a root, this proves vanishing of the
second tail by separating the coefficient two from the higher ones.
The absence of higher roots remains an explicit premise: no root-system
truncation theorem is proved here.

The provenance is the existing unit, subgroup-functor, tangent-kernel and
weight-semigroup definitions, together with the published zero-weight-space,
conjugation comparison and nonzero-multiple lemmas named above.
The geometric realization theorem is retained explicitly as
a hypothesis; this helper neither proves it nor the root-vector target.
