# NYLL cyclic norm-class evaluation and surjectivity targets

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Both targets come from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`.

| Unit | Source theorem and type lines | Adapted declaration |
| --- | --- | --- |
| M074.003 | `ClassFormation.cyclicNormClassHom_apply`, 147–167 | `Langlands.NYLL.ClassFormation.cyclicNormClassHom_applyStatement` |
| M074.006 | `ClassFormation.cyclicNormClassHom_surjective`, 269–285 | `Langlands.NYLL.ClassFormation.cyclicNormClassHom_surjectiveStatement` |

## Statements and hypotheses

Both definitions retain implicit `G : IntegralRepGroupType` with its group
and topology instances, followed by explicit `A : Rep ℤ G`, closed subgroups
`K` and `L`, containment `hLK`, normality `hnormal` of `L` within `K`,
finiteness `hfinite` of `K/L`, a specified quotient element `g`, and the
generation hypothesis `hg : ∀ x, x ∈ Subgroup.zpowers g`.
The evaluation target has the additional final explicit argument
`a : ambientFixedAddSubgroup A K`. Every binder retains its source kind and
order.

M074.003 says that applying `cyclicNormClassHom` to `a` equals the homology
projection of `cyclicFixedCycleEquiv ... a`. Its proposition retains the
normality, finiteness, `Fintype`, cyclicity and commutative-group local
instances and the local objects
`M = extensionFixedRepresentation A K L hLK hnormal` and
`T = Rep.FiniteCyclicGroup.normHomCompSub M g`.
The projection in the equality is the actual
`T.moduleCatLeftHomologyData.π`.

M074.006 asserts
`Function.Surjective (cyclicNormClassHom A K L hLK hnormal hfinite g hg)`.
Its proposition retains the same five local instances; the source does not
introduce additional `M` or `T` binders in this statement.
Both declarations are definitions returning `Prop`. They record the original
claims, without supplying their theorem proofs.

## Modifications

Prefix the namespace with `Langlands.NYLL`, append `Statement` to each
theorem name, and turn each original theorem type into the body of a
`def ... : Prop`. Omit the original proofs and the `[simp]` attribute on
M074.003. Preserve the noncomputable section and every original hypothesis.
Use the focused M074.002 definition import.

Expand `CyclicCohomology.extensionSubgroup X Y h` to
`Y.toSubgroup.subgroupOf X.toSubgroup`, the exact abbreviation body from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`.
Replace `CyclicCohomology.isCyclic_of_generator g hg`
(`NormKernelVanishing.lean:34–45`) by the Mathlib term
`isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩`.
Both terms prove the same proposition; proof irrelevance preserves the
local instances used in the target expressions. These are the same
documented replacements as in the M074.001 and M074.002 data constructions.
No extra hypothesis, global instance or alternate norm-class map is added.

## Validation and scope

Published-import development check `cd36d9da-eb91-43cb-868b-4424b2f6f149`,
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled both
targets and their full-constant comparisons with zero errors and warnings.
The private verification module `RestoredSourceCheck.lean` reconstructs the
original statement expressions using the original cyclicity helper and
original subgroup abbreviation, then checks equality of the entire unapplied
constants by `rfl`. The M074.001 and M074.002 imports are independently
accepted and published in the Library.

Exact declaration inspections against the promoted source pair
`ae7a757c-5f67-4e97-acf4-8e215c749ae8` (M074.003) and
`136e0493-4a36-43b7-b77d-9dab1831328a` (M074.006) both compiled
without errors or warnings and reported `statement_returns_prop: true`. Independent semantic review and publication
remain separate from development checks; proofs of the targets belong to
separate proof tasks.
