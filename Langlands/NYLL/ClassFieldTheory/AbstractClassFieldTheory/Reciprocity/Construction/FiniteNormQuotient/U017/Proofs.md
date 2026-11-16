# NYLL M039.017: annihilation of the finite norm quotient by the degree

The paired Lean file proves
`Langlands.NYLL.ClassFormation.finiteNormQuotient_degree_nsmul_eq_zero` with
exactly the published target
`finiteNormQuotient_degree_nsmul_eq_zeroStatement A E q` as its type.
Its parameters are implicit `G : IntegralRepGroupType` with group and
topological-space instances, explicit `A : Rep ℤ G`,
`E : DegreeData.FiniteAbstractExtension G` and
`q : FiniteNormQuotient A E.base E.field E.below`. The representation
universe is arbitrary. The finite coset-space instance comes from `E`.
The assertion is `(E.degree : ℕ) • q = 0`.

## Implemented proof

After `show` unfolds the target, the private induction lemma, supplied with
the explicit motive `fun q => (E.degree : ℕ) • q = 0`, reduces the goal to a
class `finiteNormClass ... a`. The proof unfolds `finiteNormClass` and uses
`map_nsmul`. The public `finiteNormClass_eq_zero_iff` (M039.012) identifies
vanishing with membership in the norm image. The witness is
`fixedFieldInclusion A E.base E.field E.below a`, whose norm is the required
multiple by the public M028.003 theorem `relativeNorm_fixedFieldInclusion`.

The remaining private helper `finiteNormQuotientInductionLocal` combines
M039.014 induction with its M039.013 quotient-surjectivity argument. The
identical private copy of M039.012 was removed during integration.

## Dependencies and scope

The module imports `FiniteNormQuotient.Statements`, its focused
`FiniteNormQuotient.U012.Proofs`, and
`Degree.PrimeElements.RelativeNorm.U003.Proofs`, all under
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory` (the first two
under `Reciprocity.Construction`). It uses their actual norm quotient,
vanishing criterion and norm-degree identity. No hypothesis or target
statement is changed. This support result proves no host class-formation,
cup, transfer, Tate or reciprocity statement.

## Source correspondence and attribution

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` at
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`,
lines 210–223 (M039.017 theorem 213–216, proof 217–223), with
private prerequisite proofs from M039.012 at 156–157, M039.013 at 165–170
and M039.014 at 181–182, SHA-256
`f541cbe9d1f0a01b867d7339fc7ef0eb830bd9bf799ceaadfb6506c4bb334da7`.
It is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

Worker 520's initial adaptations on 16 November 2026 are the namespace prefix
`Langlands.NYLL`, the focused published import, replacement of the source
`extensionSubgroup K L hLK` abbreviation with its exact
`L.toSubgroup.subgroupOf K.toSubgroup` body, the target-valued theorem
type, the leading `show`, the explicit induction motive, and the private prerequisite proofs under distinct
implementation names in the original submission. The unused source opens, universe declaration and surrounding sections
are omitted. The original copyright, author and Apache-2.0 header is retained
verbatim. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development verification

Development `lean_check` 53dcb4f2-847d-42c2-bd39-87871e187d8f compiled the module and inspected this
theorem in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.
The inspected assumptions are only `propext`, `Classical.choice` and
`Quot.sound`. Independent exact-target validation and semantic review are
separate publication requirements.

## Integration update

Integrator, 16 November 2026: the current implementation reuses the
independently accepted public M039.012 lemma and removes their private copies.
The dated source-modification account above records the original port;
the target and the mathematical proof are unchanged.
