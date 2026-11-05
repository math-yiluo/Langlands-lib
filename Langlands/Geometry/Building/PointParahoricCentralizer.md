# Centralizer intersections from actual point fixation

The entry `ParahoricBuildingData.centralizerParahoricEquivCentralizerZeroImage`
is an ambient-point identity multiplicative equivalence

```text
(centralizerPoints P.i ∩ P.parahoric Omega)
  ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j).
```

It applies in arbitrary universe `u` to the existing actual
`P : ParahoricBuildingData G` over a nonarchimedean local field and every
nonempty subset `Omega` of its apartment. Its explicit premises are the
apartment axioms, actual rank-one factorization
`RelativeRoot.HasRankOneFactorization P.i`, and the supplied cover comparison
`P.zeroDatum.CoverImageCentralizerNormKernelStatement`.

The intersection and image are subgroups of the actual rational-point group
`G(F)`. The full parahoric is its existing generated subgroup. The
centralizer, its inclusion, and the centralizer-zero subgroup are the
existing supplied objects.

## Implemented proof

Choose `x` in `Omega`. Antitonicity of the generated parahoric puts every
element of `P.parahoric Omega` in the point parahoric `P.parahoricAt x`.
For a centralizer point `z` whose image lies in this subgroup, the published
`normalizer_smul_eq_self_of_mem_parahoricAt` makes its original normalizer
action fix `x`, under the retained apartment and rank-one premises. The
published `parahoric_le_zeroSubgroup` also puts its image in the actual zero
subgroup, hence in the rational common norm kernel of `G`. The existing
`mem_rationalCommonNormKernel_of_smul_eq` then puts `z` in the rational common
norm kernel of the centralizer. This proves
`mem_centralizerNormKernel_of_mem_parahoric`, without using the cover
comparison.

The retained cover comparison, through the published
`centralizerZeroIntersection_of_coverImage`, identifies the intersection of
the preimage of the actual zero subgroup with this centralizer norm kernel
as the actual centralizer-zero subgroup. Thus `z` lies in `P.centralizerZero`.
Every ambient centralizer point comes from the represented centralizer
inclusion, so this proves the forward inclusion of
`centralizer_inf_parahoric_eq_of_rankOneFactorization`. The reverse inclusion
uses the existing containment of the centralizer-zero image in the
centralizer and every generated full parahoric. The theorem
`centralizerParahoricIntersection_of_rankOneFactorization` packages the same
proof as the existing `P.CentralizerParahoricIntersectionStatement` after
the two explicit algebraic inputs are supplied.

Finally `MulEquiv.subgroupCongr` of that subgroup equality gives the entry.
Both directions preserve the ambient rational point; the displayed
application lemma is reflexivity.

## Provenance and scope

This is derived content using the current Library point-exchange,
centralizer-action, norm-kernel, generated-parahoric and cover-comparison
results. No new external-source assertion is used. The proof needs no
separate boundedness premise or ordered-root-product premise.

The rank-one factorization and cover comparison remain assumptions. This
module does not prove the unchanged apartment-only centralizer-parahoric
target without those inputs, nor the apartment-only
`AffineIwahoriTitsStatement`.
