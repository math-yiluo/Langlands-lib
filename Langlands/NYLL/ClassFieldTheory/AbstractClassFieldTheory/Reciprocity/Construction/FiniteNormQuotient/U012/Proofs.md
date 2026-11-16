# NYLL M039.012: vanishing of a finite norm class

The paired Lean file proves
`Langlands.NYLL.ClassFormation.finiteNormClass_eq_zero_iff` with exactly the
published target `finiteNormClass_eq_zero_iffStatement A K L hLK a` as its
type. Its parameters are arbitrary `G : IntegralRepGroupType` with group and
topological-space instances, `A : Rep ℤ G`, closed subgroups `K L`, an
inclusion `hLK : L.toSubgroup ≤ K.toSubgroup`, a finite coset-space instance
for `K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)`, and
`a : ambientFixedAddSubgroup A K`. The representation universe is arbitrary.
It asserts that the class of `a` in `A_K / N_{L|K} A_L` is zero if and only if
`a` belongs to the relative norm image. No normality hypothesis is needed.

## Implemented proof and dependencies

After a `show` exposes the target's equivalence, the proof unfolds
`finiteNormClass`, `finiteNormClassHom` and `FiniteNormQuotient`. The result
is the ordinary additive quotient class of `a`; Mathlib's
`QuotientAddGroup.eq_zero_iff` identifies its vanishing with membership in
`finiteNormSubgroup A K L hLK`. This is exactly the original proof after the
initial `show`. There are no local helper lemmas or new assumptions. The
source `simp` attribute is retained.

The sole import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements`.
It supplies the target, finite norm quotient definitions, the relative norm
image and the ambient fixed subgroup, and imports the required Mathlib
quotient theorem. The target and all imported Lean/Markdown files are
unchanged. This support result proves no host class-formation, cup,
transfer, Tate or reciprocity statement.

## Source correspondence and attribution

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` at
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
lines 147–157 (theorem 149–155, proof 156–157), SHA-256
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
`L.toSubgroup.subgroupOf K.toSubgroup` body, a target-valued theorem type and
the leading `show`. The unused source opens, universe declaration and
surrounding sections are omitted. The original copyright, author and
Apache-2.0 header is retained verbatim. The Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain unchanged, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development verification

Development `lean_check` f15286a1-b90a-4a15-86cb-5c4ac5e9ead5 compiled the
module and inspected this theorem in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
The inspected assumptions are only `propext`, `Classical.choice` and
`Quot.sound`. Independent exact-target validation and semantic review are
separate publication requirements.
