# NYLL M039.013: every finite norm class has a representative

The paired Lean file proves
`Langlands.NYLL.ClassFormation.finiteNormClass_surjective` with exactly the published
`finiteNormClass_surjectiveStatement` applied to its parameters as the theorem type.
The common parameters are implicit `G : IntegralRepGroupType` with group
and topological-space instances, `A : Rep ℤ G`, closed subgroups `K L`,
`hLK : L.toSubgroup ≤ K.toSubgroup` and an instance
`Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))`.
The representation universe is arbitrary. The theorem also has
no further parameters.

## Implemented proof and dependencies

Introducing `q` exposes the target's `Function.Surjective` body.
The proof changes the type of `q` to its defining additive quotient, applies
Mathlib's `QuotientAddGroup.mk'_surjective` to select a representative `a`,
and returns `⟨a, rfl⟩`. Definitional equality identifies the canonical
quotient map with `finiteNormClass`. These are exactly the source proof
steps; no choice of representative is published as data and no helper or
additional assumption is introduced.

The sole import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements`.
It supplies the exact target and all finite norm quotient constructions,
and transitively the needed Mathlib additive quotient and homomorphism API.
The target and all imported Lean/Markdown files are unchanged. This support
result proves no host class-formation, cup, transfer, Tate or reciprocity
statement.

## Source correspondence and attribution

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` at
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
lines 159–170 (theorem 160–164, proof 165–170), SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
It is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

Worker 520's adaptations on 16 November 2026 are the namespace prefix
`Langlands.NYLL`, the focused published import, replacement of the source
`extensionSubgroup K L hLK` abbreviation with its exact
`L.toSubgroup.subgroupOf K.toSubgroup` body, and the target-valued theorem
type. The unused source opens, universe declaration and surrounding sections
are omitted. The original copyright, author and Apache-2.0 header is retained
verbatim. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development verification

Development `lean_check` eb025269-6a0e-4fb2-8f22-b53ef6d8bbc3 compiled the module and inspected this
theorem in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
The inspected assumptions are only `propext`, `Classical.choice` and
`Quot.sound`. Independent exact-target validation and semantic review are
separate publication requirements.
