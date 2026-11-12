# Canonical map on actual norm-one adelic Weil points

Let `F` and `L` be number fields in arbitrary common universe `u`, with a
specified `Algebra F L`, and let `G` be any affine group scheme locally of
finite type over `L`. This module constructs
`AdelicWeilRestriction.normOneMap F L G`, a continuous group homomorphism

```text
normOneSubgroup F (AffineWeil.groupScheme F L G) →ₜ* normOneSubgroup L G.
```

Its underlying map is exactly the restriction of the published canonical
`adelicPointsEquiv F L G`. Both norm-one subgroups are the original
intersections of the normalized absolute-value kernels of all rational
algebraic characters, with their original subgroup topologies.

`characterNorm_normCharacter_apply` proves that the normalized value of a
transferred norm character on a ground-field adelic point is exactly the
normalized value of the original upper-field character on its canonical Weil
image. The proof composes two exact identities: the published actual
idele-valued evaluation formula for `normCharacter`, and
`AdelicFunctoriality.full_ideleNorm` from `IdeleNormAbsoluteValue`.

If a ground-field point lies in the full norm-one subgroup, its norm is one
for every transferred upper-field character. The preceding identity gives
norm one for every upper-field character of its image.
`adelicPointsEquiv_mem_normOne` states this pointwise;
`map_normOneSubgroup_le` states the corresponding subgroup-image inclusion.
Restricting the canonical multiplicative equivalence to these subgroups then
defines `normOneMap`. Continuity follows from the published homeomorphism
property of that same canonical equivalence and the subgroup topologies.

`normOneMap_injective` retains the injectivity of the ambient equivalence.
`isClosedEmbedding_normOneMap` also retains the original topology: the source
norm-one subgroup is closed, so its inclusion followed by the ambient
homeomorphism is a closed embedding. Factoring this composite through the
target subgroup inclusion proves that the restricted map is a closed
embedding.
`normOneMap_rational` proves preservation of every actual principal point
by the already published principal compatibility of `adelicPointsEquiv`.

This is an internal consequence of the named constructions and identities.
It requires no commutativity, reductivity, connectedness or splitting
hypothesis on `G`, and no Galois hypothesis on `L/F`.
It proves only the displayed inclusion of norm-one subgroups. Surjectivity,
the reverse inclusion, classification of all ground-field characters and the
full `NormOneComparisonStatement` remain separate obligations.
