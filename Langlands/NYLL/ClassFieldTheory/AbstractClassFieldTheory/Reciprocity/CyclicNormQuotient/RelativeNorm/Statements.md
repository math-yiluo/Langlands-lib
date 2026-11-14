# NYLL cyclic fixed-cycle comparison with the relative norm

Worker 196, 14 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source module is
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`,
SHA-256 `6dc5f10e7546a7b85d7712388b443344fe87679ef13d0eadb0f3451f925c731a`.
The original copyright and author header is retained; see the Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

| Unit | Source theorem and type lines | Adapted declaration |
| --- | --- | --- |
| M074.004 | `ClassFormation.cyclicFixedCycleEquiv_relativeNorm`, 172–193 | `Langlands.NYLL.ClassFormation.cyclicFixedCycleEquiv_relativeNormStatement` |

## Statement and complete telescope

The source implicit `{G : IntegralRepGroupType}`, `[Group G]` and
`[TopologicalSpace G]` (source lines 33–34) remain unchanged. In order, the
explicit parameters are `A : Rep ℤ G`, closed subgroups `K L`, containment
`hLK`, normality `hnormal` of `L` in `K`, finiteness `hfinite` of `K/L`, a
quotient element `g`, the generation hypothesis
`hg : ∀ x, x ∈ Subgroup.zpowers g`, and
`a : ambientFixedAddSubgroup A L`. Every binder retains its source kind.
The published `IntegralRepGroupType` is `Type 0`; the representation's
universe constraints come from the unchanged source constructions.

The proposition retains all five source local instances: normality,
finiteness, `Fintype.ofFinite`, cyclicity from the specified generator,
and `IsCyclic.commGroup`. It then retains the local objects
`M = extensionFixedRepresentation A K L hLK hnormal` and
`T = Rep.FiniteCyclicGroup.normHomCompSub M g`.

It says that applying the published fixed-cycle equivalence to
`relativeNorm A K L hLK a` equals applying `T.moduleCatToCycles` to
`(extensionFixedRepresentationEquiv A K L hLK hnormal).symm a`.
Thus the actual relative norm corresponds to the first differential into
cycles in this concrete cyclic Tate complex. The fixed subgroup,
representation, equivalence and norm are actual published objects.
The file defines this equality as a proposition; it provides no theorem proof.

## Modifications and published dependencies

Prefix the namespace with `Langlands.NYLL`, append `Statement`, and turn
the source theorem type into a `def ... : Prop`. Omit the source proof
at lines 194–199. Retain the source noncomputable section and every binder,
local instance and local object. Replace the broad original imports with
`CyclicNormQuotient.FixedCycle.Definitions` (M074.001 and its published
M073.001 dependency) and `Degree.Norm.RelativeNorm.Definitions` (M024.009).

Expand `CyclicCohomology.extensionSubgroup K L hLK` to its exact Mathlib
body `L.toSubgroup.subgroupOf K.toSubgroup`, from the same pinned source's
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`.
The containment witness remains in the telescope.
Replace `isCyclic_of_generator g hg` (that source file's lines 34–45) by
`isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩`.
These prove the identical `IsCyclic` proposition; proof irrelevance preserves
the dependent uses of this witness in the local commutative-group instance.
These are the documented replacements already used by the published
fixed-cycle equivalence. No additional hypothesis, map or global instance
is introduced.

## Verification and scope

The private source comparison reconstructs the full source statement with
the original subgroup abbreviation and the original generator-cyclicity
helper, and checks equality of the entire unapplied constants by `rfl`.
Development compilation and exact Prop inspection use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean v4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Source comparison `1a71b80f-7c5c-4fa1-9b29-ad8cdd370ce9` and exact
inspection `b5a8b53d-8fde-4390-9765-d0896ae614b5` both finish with zero
errors and warnings; inspection reports `statement_returns_prop: true`
and no universe parameters, matching the source objects. Development checks do not supply
independent semantic acceptance or the separate proof of this target.
