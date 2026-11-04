# Normality of codimension-one connected unipotent subgroups

This internal construction derives a normalizer enlargement and normality of
closed subgroups of codimension at most one from results already in the Library.
It works over every field, in every characteristic and at universe `u`.
Worker 317 identified the normality input needed in the prescribed-Borel
approach to rank-one positive-root uniqueness; Worker 1547 implemented the
universal commutator and generated-subgroup argument here.

The ambient group `G` and supplied subgroup `H` are smooth, connected and affine
over `k`, and `j : H ⟶ G` is an actual closed subgroup inclusion. The general
results assume `∃ d, HasUniformNilpotentPoints G d`: a single bound kills the
lower central series of the group of points over every relative scheme test.
The unipotent specialization obtains this bound from the published theorem
`exists_hasUniformNilpotentPoints_of_isUnipotent`; it does not assume a
nilpotence theorem separately.

`exists_smoothConnected_normalizer_enlargement` assumes additionally that the
subgroup functor `range j` is proper. It produces an actual smooth connected
affine group `K` with a closed inclusion `i : K ⟶ G` such that
`range j < range i ≤ (range j).normalizer`. Both containments concern all
scheme-valued points, including nonreduced and nonaffine tests.
`SmoothConnectedNormalizerEnlargement j` packages these data and properties.
`smoothConnectedNormalizerEnlargement_of_uniformNilpotence` chooses such data
classically under the same assumptions; no canonical choice is asserted.

The proof uses the published iterated universal commutator words.
`IteratedCommutator.exists_last_word_not_contained` chooses the word immediately
before the first word whose entire image lies in `range j`. Properness excludes
the zeroth word, which is the identity morphism of `G`, while uniform nilpotence
supplies a word with constant identity value.
`normalizer_containsImage_of_succ_contained` puts the preceding word image in
the full normalizer functor after every refinement. For the forward conjugation
direction, multiply the commutator `[g,x]` by `x`. For the inverse direction, use
the inverse of `[g,g⁻¹ x g]` and multiply by `x`. The next-word hypothesis applies
to every ambient point, so it applies to `g⁻¹ x g` without assuming that this
point already belongs to the subgroup.

Form the pointed morphism from `H × source G n` to `G` given on points by
`(h,v) ↦ j(h) * word(v)`. The source is affine, locally of finite type and
geometrically integral, by `smoothConnectedAffineGeometry`,
`IteratedCommutator.source_good` and `finitePowerGood_tensor`.
`ImageGeneration.pointedImageGeneration` gives its smooth connected closed
generated subgroup. Setting `v` to the identity tuple includes `H`; setting `h`
to the identity includes the preceding commutator word. This latter image
proves strict enlargement. The whole pointed image lies in the normalizer.
The normalizer has a closed representative by
`hasClosedRepresentative_normalizer_centralizer_range`, so minimality of the
closed image envelope puts the generated subgroup in that normalizer.
No smoothness of the normalizer itself is required.

`isNormal_of_lieDimension_le_succ_of_uniformNilpotence` assumes
`Lie.dimension G ≤ Lie.dimension H + 1` and proves
`(SubgroupFunctor.range j).IsNormal`. Here `Lie.dimension` is the finite dimension
of the actual dual-number Lie kernel over `k`. In the proper case, factor `j`
through the enlargement `K`. The factor is a closed subgroup inclusion by
`IsClosedSubgroup.of_comp` and is not an isomorphism because the enlargement is
strict. Thus `Lie.dimension H < Lie.dimension K`. If `K ⟶ G` were also proper,
`dimension_lt_of_proper_closedSubgroup` would give
`Lie.dimension K < Lie.dimension G`, contradicting the assumed bound.
Consequently `K ⟶ G` is an isomorphism, and every point of `G` belongs to the
normalizer. The case `range j = ⊤` is immediate.
`isNormal_of_lieDimension_le_succ_of_isUnipotent` specializes this result to
`IsUnipotent G`.

This is a derived helper, not a proof of positive-root uniqueness. It does not
construct a Borel quotient, bound its dimension, compare dynamic subgroups with
a prescribed Borel, or assert equality from equal Lie algebras of incomparable
subgroups. Its dimension argument uses actual closed subgroup factorizations.
