# Normalized Haar comparison between actual split components

Author: Worker 112.

This internal construction uses `AdelicLogSection` and
`AdelicNormOneDecomposition` for the actual character-log equivalences,
`AdelicSplitComponentIndependence` for equality of actual images, and
`AdelicSplitCenterHaarIndependence` for uniqueness under fixed ambient and
norm-one Haar normalization. The full subgroup measure and multiplication
chart come from `AdelicSplitCenterSubgroupHaar`. It adds no external
existence theorem.

Let `F : Type u` be a number field, `G/F` an actual group scheme, and
`i : T.toGrp ⟶ G`, `i' : T'.toGrp ⟶ G` actual maps from commutative group
schemes with supplied finite splittings `e` and `e'`. Retain explicit
injectivity of each `characterRestrict` and finite index of each range.
`positiveComparisonEquiv` is a continuous group equivalence between the
existing `intrinsicSubgroup F T` and `intrinsicSubgroup F T'`. Both identify
with the same ambient character-log dual through `positiveAmbientLogEquiv`;
compose the first equivalence with the inverse of the second. This
construction requires neither centrality nor an equality of positive
images.

`positiveComparisonEquiv_apply` expresses the comparison as the target's
`positiveFactor` applied to the source's actual ambient point. If the
actual positive images agree as subgroups of the ambient adelic group,
`positivePointMap_positiveComparisonEquiv` says that the comparison
preserves ambient points. Express the first image point as an image from
the second positive group, then apply the second positive factor, which
recovers that positive point.

`measurePreserving_positiveComparisonEquiv` proves exact transport of the
existing `normalizedPositiveHaarMeasure` measures, retaining centrality of
both maps, equality of their actual positive images, and
`[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]`. Push the first
positive measure through the comparison and multiply it by the unchanged
norm-one Haar. The product-map identity and ambient point formula show
that its pushforward through the second multiplication chart equals the
fixed ambient Haar. Uniqueness for the second normalization gives the
claimed exact equality of measures. Sigma-finiteness needed by the
product-map identity follows from the existing normalized Haar theorem.
There is no change of ambient or norm-one Haar choice and no scalar left
to choose.

For two supplied actual split components, `splitComponentSubgroupEquiv`
uses the existing literal equality of the positive-times-principal
subgroups. It preserves ambient representatives and is continuous in both
directions for their inherited subgroup topologies.
`splitComponentSubgroupEquiv_positiveRationalDecomposition` proves that
the comparison commutes with actual multiplication, using
`positiveComparisonEquiv` on the positive factor and the identity on the
unchanged principal norm-one subgroup.

`measurePreserving_splitComponentSubgroupEquiv` proves exact transport
between the existing `positiveRationalSubgroupHaarMeasure` measures.
Tensor the positive comparison's measure-preserving property with that
of the identity on `rationalNormOneSubgroup F G` equipped with counting
measure. The multiplication commutation formula identifies the composite
pushforwards with the pushforward defining the target full subgroup Haar.
Thus the identity on ambient representatives preserves the full
normalization, not merely its measure class. Both actual split-component
hypotheses supply centrality; character injectivity and finite index
remain explicit additional hypotheses of this result.

`measurePreserving_positiveComparisonEquiv_intrinsic` gives the analogous
positive-measure assertion for the existing `intrinsicPositiveHaarMeasure`
constructions from supplied split-torus properties. Rewrite each intrinsic
measure by its comparison with the supplied splitting, then use the
normalized positive transport theorem.
`measurePreserving_splitComponentSubgroupEquiv_intrinsic` compares
`intrinsicPositiveRationalSubgroupHaarMeasure` for the two actual split
components. This theorem has no supplied splitting coordinates. Extract a
finite splitting from each split-component hypothesis, rewrite by the
existing intrinsic-measure comparison laws, and apply full subgroup
transport. Its identity-on-representatives comparison also has no
coordinate arguments.

The finite coordinate sets may be empty. Injectivity and finite index of
each character restriction remain explicit in the measure comparisons.
The subgroup equivalence itself uses only supplied split components and
the affine locally finite type assumptions. The algebraic hypotheses
ensure equality of actual subgroups; no substitute point group or
transported topology is introduced. These results do not compare different
ambient or norm-one Haar choices or the initial unnormalized coordinate
Haar. They do not identify these split components with the greatest
rational split centre after restriction of scalars, prove general
reductive decomposition, or prove finite volume or reduction theory.
