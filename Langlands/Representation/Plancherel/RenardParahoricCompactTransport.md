# From parahoric to maximal-compact Cartan representatives

This internal reduction is part of Task 5309. It leaves every unproved
geometric prerequisite explicit and does not establish
`AvailableRenardCartanStatement`.

The group-theoretic lemma `compactComparison_of_parahoric` transports
coverage and the forward double-coset classification from a subgroup
`P` to a larger subgroup `K`. Its premises identify the preimage of `K`
under the centralizer map with a normal subgroup `N`, require the image
of `N` to normalize `P`, and require the dominant set to be stable under
multiplication on either side by `N`. Parahoric coverage first writes
every element of `K` as `j(n)p` and as `p'j(n')`. Substitution in a
`K` double-coset relation gives a `P` relation between two dominant
centralizer elements; the smaller comparison then identifies their
classes modulo `N`.

For the actual building data,
`compact_comap_le_normKernel` pulls a compact subgroup back along the
closed centralizer immersion. It uses
`isClosedEmbedding_rationalPointMap` and
`compactSubgroup_le_rationalCommonNormKernel`.
`specialCompactCentralizer_comap` combines this with the published
`IsOmegaCompatible.map_mem_compactStabilizer`, giving exactly the
preimage `Z(F)^1` of the geometrically fixed `K₀`.
`specialCompactCentralizerNormEquiv` packages this as a multiplicative
equivalence that is the identity on actual centralizer points.

`specialCompactCartanComparison_of_parahoric` applies the group lemma
with `P = B.parahoricAt x`, `K = B.apartment.specialCompactSubgroup x`
and `N = rationalCommonNormKernel B.centralizer.Z`.
`normalizerStabilizer_mem_parahoric_normalizer` and
`IsOmegaCompatible.smul_eq_self` supply normalization, using the explicit
normality hypothesis on `B.normalizerZero`. The dominant-set stability
comes from `centralizerValuation_ker`; the parahoric classification has
values in `centralizerZero`, which is contained in the norm kernel by
`ZeroSubgroupDatum.centralizerZero_le_rationalCommonNormKernel`.

The retained premises are the parahoric Cartan conclusions, the inclusion
`P ≤ K₀`, compactness of `K₀`, and normality of the zero normalizer.
This file neither proves nor assumes their global availability statements.
The final proof task may use this reduction only after those prerequisites
are discharged by published proofs under the original local-availability
hypothesis. Same-compact Levi coverage and classification remain separate.

This is derived content about the Library's actual groups and maps. Its
geometric target has the source provenance documented in
`AvailableRenardCartanStatement.md`.

Author: Worker 163.
