# Semigroup subgroups with no occurring tangent weights

This internal module proves the empty-weight case of semigroup subgroup
realization without assuming the general realization theorem. The ambient
group scheme is affine over an arbitrary field and universe, and the given
action is an actual automorphic action of a split torus. Ambient smoothness,
connectedness and local finite type are not needed for the vanishing result.

First, a connected affine group locally of finite type representing an
all-test subgroup with zero tangent image represents the identity subgroup.
The existing tangent-image comparison identifies this image with the range
of the actual linear differential. Its zero range and injectivity force the
source Lie kernel to be trivial. The published
`Lie.points_eq_one_of_subsingleton_lieKernel` then gives triviality on every
scheme test. In particular this applies to a smooth connected closed
subgroup, whose affineness follows from closedness and whose local finite
type follows from smoothness.

For an invariant subgroup with an affine locally finite-type representative,
the published split-torus decomposition expresses its tangent image as the
sum of its intersections with the ambient character spaces. If the support
is empty, each intersection is zero by the definition of support. Hence the
tangent image is zero. Combining these facts proves that a smooth connected
invariant closed subgroup with empty support is the identity subgroup.

If a semigroup selects no occurring ambient tangent weight, every admissible
generator has empty support: any weight in its support would be both in the
semigroup and in the ambient support. Every generator is therefore trivial.
The existing universal property of the generated subgroup proves that the
semigroup subgroup is the identity subgroup on all tests. The empty semigroup
is an immediate specialization.

`noAmbientWeightsRepresentativeIso` uses the resulting equality and the
published uniqueness isomorphism between representatives of the same
all-test subgroup. It identifies any representative of this semigroup
subgroup with the actual trivial group scheme. This last construction does
not require smoothness, affineness or finite type of the chosen representative.

These are derived consequences of the current tangent, decomposition,
zero-tangent triviality and represented-subgroup interfaces. Existing
conditional results in `WeightSupportVanishing` retain their signatures.
This module does not construct the general semigroup realization or a
nontrivial split-unipotent series.
