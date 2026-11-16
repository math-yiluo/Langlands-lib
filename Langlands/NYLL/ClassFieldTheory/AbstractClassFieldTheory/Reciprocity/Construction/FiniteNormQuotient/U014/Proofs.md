# NYLL M039.014: induction on a finite norm class

The paired Lean file proves
`Langlands.NYLL.ClassFormation.FiniteNormQuotient.induction_on` with exactly
`FiniteNormQuotient.induction_onStatement A K L hLK q h` as its type. Its
parameters are implicit `G : IntegralRepGroupType` with group and
topological-space instances, `A : Rep ℤ G`, closed subgroups `K L`,
`hLK : L.toSubgroup ≤ K.toSubgroup`, a finite coset-space instance for
`K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)`, an implicit predicate
`motive : FiniteNormQuotient A K L hLK → Prop`, a class `q`, and
`h : ∀ a, motive (finiteNormClass A K L hLK a)`. The representation universe
is arbitrary. The conclusion is `motive q`.

## Implemented proof and dependencies

A leading `show motive q` unfolds the published target. The proof obtains
`⟨a, rfl⟩` from the private `finiteNormClassSurjectiveLocal` and finishes
with `h a`. These are the two source M039.014 steps with its source
surjectivity call replaced by a private proof. The source `elab_as_elim`
attribute is omitted because Lean rejects its eliminator check on the named
proposition used as the required theorem type. This changes no assertion or
proof step.

The private lemma is the unchanged proof of source M039.013: introduce a
quotient class, change its type to the defining additive quotient, use
Mathlib's `QuotientAddGroup.mk'_surjective`, and return the representative
with `rfl`. At preparation, the separately staged M039.013 proof was not
published; this allowed private dependency keeps the candidate independent
of its publication. It exports no duplicate declaration under the adapted
source name.

The sole import is the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements`.
It supplies the exact target and all finite norm quotient definitions, and
transitively the Mathlib quotient surjectivity theorem. No additional
mathematical assumption is introduced. The target and imported Lean/Markdown
files are unchanged. This support result proves no host class-formation,
cup, transfer, Tate or reciprocity statement.

## Source correspondence and attribution

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` at
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
lines 159–182 (private M039.013 proof 165–170; public M039.014 theorem 174–180, proof 181–182), SHA-256
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
`L.toSubgroup.subgroupOf K.toSubgroup` body, the target-valued theorem
type, the leading `show`, and a private copy of the source M039.013 proof
under a distinct implementation name. The `elab_as_elim` attribute is omitted
for the reason above. The unused source opens, universe declaration and surrounding sections
are omitted. The original copyright, author and Apache-2.0 header is retained
verbatim. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development verification

Development `lean_check` ad9c472b-68b3-43f5-8802-58734eb67ae6 compiled the module and inspected this
theorem in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
The inspected assumptions are only `propext`, `Classical.choice` and
`Quot.sound`. Independent exact-target validation and semantic review are
separate publication requirements.
