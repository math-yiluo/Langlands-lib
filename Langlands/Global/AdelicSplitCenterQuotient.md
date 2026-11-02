# Actual positive-central rational quotient and norm-one comparison

Author: Worker 112.

Let `F` be a number field, `G` an actual group scheme over `Spec F`,
`T` an actual commutative group scheme, and `i : T.toGrp ⟶ G` an actual
morphism. The definition `positiveRationalSubgroup` is the supremum of
the existing intrinsic positive image `imageSubgroup F T G i` and the
existing principal rational subgroup in the actual group `G(A_F)`.
`PositiveRationalQuotient` is its left homogeneous quotient, with the
existing quotient topology and positive right translation `[x] ↦ [x * g]`.
The rational subgroup need not be normal. These definitions require no
splitting or centrality assumption.

For the comparison, assume `G` is affine, supply a finite split-torus
isomorphism for `T`, and retain injectivity of the actual character
restriction `characterRestrict i` and finite index of its range. Also
assume actual scheme-theoretic centrality `GroupScheme.IsCentral i`.
The previous explicit `normOneFactor` becomes the continuous homomorphism
`normOneProjection`, using the second coordinate of the inverse topological
group decomposition. It fixes actual norm-one points, sends positive
point images to the identity, and sends a principal point to precisely its
principal norm-one counterpart.

The theorem `positiveRationalSubgroup_eq_comap` identifies the generated
subgroup with the inverse image of the actual principal subgroup of the
norm-one group under this constructed projection. For one inclusion, both
generators map into the principal subgroup. Conversely, if the norm-one
factor is principal, the explicit decomposition writes the original point
as a positive image times a principal point. In particular,
`mem_positiveRationalSubgroup_iff` proves that the subgroup consists
exactly of points `positivePointMap a * rational q`, in that order.
It is therefore the actual product subgroup under these hypotheses,
not merely an unspecified generated subgroup.

Inclusion of norm-one points descends to `normOneToPositiveQuotient`.
The projection descends to `positiveQuotientToNormOne` by the comap
identity. Their inverse laws follow from the factorization: the projection
fixes norm-one representatives, while removing a positive left factor does
not change the positive rational quotient class. The quotient universal
property proves continuity of both maps. They give
`positiveQuotientHomeomorph`, with forward formula
`[n] ↦ [n]` and inverse `[x] ↦ [normOneFactor x]`.
No locally finite type assumption is needed for this homeomorphism.

The right-translation identity holds for every ambient element `g`:
translation by `g` on the positive rational quotient corresponds, under
this homeomorphism, to positive translation by `normOneProjection g` on
the norm-one principal quotient. This follows from multiplicativity of
the projection and its identity on the norm-one subgroup.

If the structure morphism of `G` is locally of finite type, the actual
principal norm-one subgroup is closed. Its inverse image proves
`isClosed_positiveRationalSubgroup`, and hence the displayed quotient is
Hausdorff. Local compactness descends through the actual open homogeneous
quotient projection for affine locally finite type `G`; this last instance
needs no splitting, character-restriction or centrality input.

## Provenance and boundary

This is an internal construction from `AdelicNormOneDecomposition`,
`AdelicGroupQuotient`, the actual principal product formula, and the
quotient universal property. The implemented argument constructs both
quotient maps and proves their inverse laws; a comparison homeomorphism
is not supplied as data. All groups and subgroups are those of actual
scheme points.

The supplied torus is not identified here with the greatest Q-split centre
of the restriction of scalars in Getz–Hahn's convention. That identification,
the existence of suitable split components for general reductive groups,
and the general injective finite-index restriction theorem remain separate
obligations. The construction includes rank zero but makes no reductive,
connectedness or smoothness assumption. Compatible Haar and quotient measure
transport, Haar normalization, analytic unimodularity, reduction coverage,
and finite volume are not asserted in this unit.
