# NYLL cyclic norm-class homomorphism

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module:
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`.
M074.002, lines 117–140 (declaration at 119):
`ClassFormation.cyclicNormClassHom` maps to
`Langlands.NYLL.ClassFormation.cyclicNormClassHom`.
It is a same-module data prerequisite of M074.003, M074.005 and M074.006.

## Meaning and construction

Let `G` be the source universe-zero acting group with its group and topology
instances, and let `A : Rep ℤ G`. For closed subgroups `L ≤ K`, a normality
witness for `L` within `K`, a finiteness witness for `K/L`, and a specified
generator `g` with `hg : ∀ x, x ∈ Subgroup.zpowers g`, the result is an actual
additive homomorphism from the ambient fixed subgroup `A_K` to the concrete
degree-zero cyclic homology object.

Set `M = extensionFixedRepresentation A K L hLK hnormal` and
`T = Rep.FiniteCyclicGroup.normHomCompSub M g`. The map is the composite
of `cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg`, viewed as an
additive homomorphism to the cycle module, with
`T.moduleCatLeftHomologyData.π.hom.toAddMonoidHom`, the quotient map from
cycles to homology. Thus its codomain is exactly
`T.moduleCatLeftHomologyData.H`. The original `intro` of the local instance
and object binders, the local equivalence `e`, and the composition expression
are retained.

The complete telescope is implicit `G : IntegralRepGroupType`, its group and
topology instances, then explicit `A`, `K`, `L`, `hLK`, `hnormal`, `hfinite`,
`g` and `hg`, in source order. The result type retains the source local
normality, finiteness, `Fintype`, cyclicity and commutative-group instances,
followed by the local objects `M` and `T`. It adds no global instance or
extra hypothesis.

## Modifications

Prefix the namespace with `Langlands.NYLL`. Replace the three broad source
imports by the focused M074.001 fixed-cycle definition import, which supplies
the constructions and Mathlib imports used here. Retain the noncomputable
section and the original data construction.

Expand `CyclicCohomology.extensionSubgroup X Y h` to its exact Mathlib body
`Y.toSubgroup.subgroupOf X.toSubgroup`, as defined in
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`.
Keep the explicit source containment witness `hLK`.

Replace source M004.001 `CyclicCohomology.isCyclic_of_generator g hg`
(`NormKernelVanishing.lean:34–45`) by
`isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩`.
Both prove the same cyclicity proposition, so proof irrelevance preserves
the subsequent construction. This is the same documented Mathlib replacement
used for M074.001; Worker 5264 was informed of it during that preparation.
No other term of this data construction changes.

## Validation and scope

Development check `1e62bade-93c3-4f00-8ed3-2ac8e7476b51`, in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled the definition
and `RestoredSourceCheck.lean` with zero errors and warnings. The comparison
module reconstructs the original cyclicity helper, M074.001 and M074.002
and proves equality of the complete unapplied source and adapted constants
by `rfl`. This checks the full telescope and construction, including local
instances and proof terms.

The check uses the independently published M074.001 prerequisite from Library
`6948120d6f1b811bab3b7ee04997f6fba7aa9908`; no private prerequisite module
overrides its import. Development checks do not establish independent
acceptance or publication. The definition constructs the homology-class map;
the identification of its kernel with a relative-norm subgroup is a separate
statement.
