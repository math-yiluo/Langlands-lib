# NYLL M011.002: index of the additive degree image

`Langlands.NYLL.ClassFormation.DegreeData.fieldImageAdd_index` proves exactly
`Langlands.NYLL.ClassFormation.DegreeData.fieldImageAdd_indexStatement D K`
for `{G : Type*} [Group G] [TopologicalSpace G]`, `D : DegreeData G`, and
`K : FiniteResidueAbstractField D`. Thus the additive subgroup
`D.fieldImageAdd K.field` has index `(K.residueDegree : ℕ)` in `ZHat`.
All parameters and hypotheses are those of the published target.

## Source and attribution

The source is Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`,
lines 33–39 (the `@[simp]` attribute is line 32), at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. Its SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The original 2026 copyright and author header (Naganori Yamaguchi,
assisted by OpenAI Codex) is retained. The existing Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable and
unchanged. Worker 5264 supplied the adapted proof body in Task 6485
revision 3; Worker 356 packages it here with the source attribution and
this proof explanation.

## Implemented proof and dependencies

The proof follows the original route. Unfolding the target and the additive
image through `Subgroup.toAddSubgroup'` changes the index to the index of
`D.fieldImage K.field`. Rewriting with
`Subgroup.relIndex_top_right` changes that index to the cardinality of the
actual residue quotient `D.residueQuotient K.field`. The symmetric form of
the published M010.026 theorem
`DegreeData.FiniteResidueAbstractField.residueDegree_coe K` identifies this
cardinality with the natural value of `K.residueDegree`.

The direct imports are the unchanged published
`Degree.Frobenius.FieldImageIndex.Statements` module and
`Degree.Fields.FiniteResidue.U026.Proofs`, both below
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory`. The statement
imports the degree datum, finite-residue definitions, additive degree
image, and Mathlib index API. No extra field hypothesis is introduced.

## Modifications

The source namespace receives the `Langlands.NYLL` prefix. The theorem's
conclusion is the exact named target proposition, with the source variable
declaration and explicit `D` and `K` preserved. The whole-source `Fields`
import is replaced by the two focused published imports. The final source
method call `K.residueDegree_coe` is explicitly qualified. The source
`@[simp]` attribute is omitted because this theorem is stated through the
opaque target proposition. No published statement or definition is edited.
