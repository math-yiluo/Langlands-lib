# NYLL cyclic norm-class kernel target

Worker 196, 16 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source is
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`,
SHA-256 `6dc5f10e7546a7b85d7712388b443344fe87679ef13d0eadb0f3451f925c731a`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

| Unit | Source declaration and type lines | Adapted declaration |
| --- | --- | --- |
| M074.005 | `ClassFormation.cyclicNormClassHom_ker`, 203–219 | `Langlands.NYLL.ClassFormation.cyclicNormClassHom_kerStatement` |

## Exact statement and telescope

The target says that the kernel of the concrete cyclic Tate-class additive
homomorphism `cyclicNormClassHom A K L hLK hnormal hfinite g hg` equals
`finiteNormSubgroup A K L hLK`. The latter is the published actual range of
`relativeNorm A K L hLK` inside `ambientFixedAddSubgroup A K`.
The class map is the published fixed-cycle equivalence followed by the
projection to the concrete cyclic homology quotient. Both sides are actual
constructions, with no assumed kernel identity.

The implicit source group `{G : IntegralRepGroupType}`, `[Group G]` and
`[TopologicalSpace G]` (source lines 33–34) are retained.
`IntegralRepGroupType` is the source's `Type 0` scope. In source order, the
explicit parameters are `A : Rep ℤ G`, closed subgroups `K L`, containment
`hLK : L.toSubgroup ≤ K.toSubgroup`, normality `hnormal`, finiteness
`hfinite` of the coset quotient, a quotient element `g`, and
`hg : ∀ x, x ∈ Subgroup.zpowers g`. All binder kinds are unchanged.
The quotient occurring in these binders is exactly `K/L` in the source's
subgroup convention.

The body retains all five local instances in order: the supplied normality,
the supplied finiteness, `Fintype.ofFinite`, cyclicity from `g` and `hg`,
and `IsCyclic.commGroup`. It then states the equality of additive subgroups.
No class-field axiom, degree datum or additional hypothesis occurs.
This file defines the proposition and does not prove it.

## Modifications and dependencies

Prefix the source namespace with `Langlands.NYLL`, append `Statement`, and
replace the source theorem by a `def ... : Prop :=` of its exact type.
Omit the source proof, lines 220–265, and use focused published imports:
`CyclicNormQuotient.NormClass.Definitions` (M074.002) and
`Construction.FiniteNormQuotient.Definitions` (M039.001, the actual norm
range). The source noncomputable section is retained. Unused broad opens
are narrowed to the existing namespaced Kummer, cyclic-cohomology and
category namespaces; this changes no mathematical object.

Expand `CyclicCohomology.extensionSubgroup K L hLK` to its precise body
`L.toSubgroup.subgroupOf K.toSubgroup`, from the pinned source's
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`.
Retain the containment witness, including every original occurrence where
its value is unused by that abbreviation. Replace the source helper
`isCyclic_of_generator g hg` (the same file, lines 34–45) by
`isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩`.
Both are proofs of the same `IsCyclic` proposition. Proof irrelevance
preserves its dependent uses in the commutative-group instance, as in the
published norm-class construction. No new map or global instance is added.

## Verification and scope

The private source comparison reconstructs the complete original theorem
type with `extensionSubgroup` and the original generator-cyclicity helper,
and compares the entire unapplied target with it by `rfl`.
Development compilation and exact proposition inspection use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean v4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). These checks supply neither
independent semantic acceptance nor the separate theorem proof.

Source comparison `5a568162-08af-486b-9930-e6bff7ad4037` and exact inspection
`91538b0b-5ebf-462a-9d08-48c167ef29ad` both pass with zero errors and
warnings. Inspection reports `statement_returns_prop: true` and no universe
parameters, matching the retained source scope.
