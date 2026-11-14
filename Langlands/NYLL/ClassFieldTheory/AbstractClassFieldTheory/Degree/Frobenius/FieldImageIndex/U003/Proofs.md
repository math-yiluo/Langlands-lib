# NYLL M011.003: the additive degree image is the residue-degree multiple range

`Langlands.NYLL.ClassFormation.DegreeData.fieldImageAdd_eq_mulNat_range`
proves exactly
`Langlands.NYLL.ClassFormation.DegreeData.fieldImageAdd_eq_mulNat_rangeStatement D K`
for `{G : Type*} [Group G] [TopologicalSpace G]`, `D : DegreeData G`, and
`K : FiniteResidueAbstractField D`. The asserted equality of additive
subgroups of the actual closure model `ZHat` is

```lean
D.fieldImageAdd K.field =
  (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range
```

## Source and attribution

The source is Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`,
lines 42–48 for M011.003 and lines 33–39 for its M011.002 prerequisite,
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The source file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The original 2026 copyright and author header (Naganori Yamaguchi,
assisted by OpenAI Codex) is retained. The existing Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable and
unchanged. Worker 5264 supplied both adapted proof bodies in Task 6485
revision 3. Worker 356 packages M011.003 here and makes its prerequisite
private so this candidate depends only on published imports.

## Implemented proof and dependencies

The private `u003_fieldImageAdd_index` lemma repeats the original M011.002
proof. It changes from the additive degree image to `D.fieldImage K.field`,
rewrites the subgroup index with `Subgroup.relIndex_top_right`, changes to
`Nat.card (D.residueQuotient K.field)`, and finishes with the symmetric
published M010.026 theorem
`DegreeData.FiniteResidueAbstractField.residueDegree_coe K`. This is a
local proof of the already published index target, under a private,
non-conflicting name; it does not introduce another public M011.002 theorem.

The main proof applies the published M009.013 theorem
`Langlands.NYLL.ClassFormation.zHatAddSubgroup_eq_mulNat_range_of_index_eq`
to `D.fieldImageAdd K.field`, the positivity
`K.residueDegree.property`, and the private index lemma. The conclusion of
that theorem unfolds to the required target. No closedness or additional
group or field hypothesis is introduced.

The direct imports are the unchanged published
`Degree.Frobenius.FieldImageIndex.Statements` and
`Degree.Fields.FiniteResidue.U026.Proofs` modules below
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory`, and
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U013.Proofs`.

## Modifications

The source namespace receives the `Langlands.NYLL` prefix. The theorem
retains the source variable declaration and explicit `D`, `K` binders and
concludes the exact named target proposition. The original broad `Fields`
import is replaced by focused published imports. The source's application
of the subgroup classification is expressed as a direct proof term. The
source call to M011.002 is replaced by its private local proof so the two
critical-path candidates can be independently staged before either is
published. No source `@[simp]` attribute belongs to M011.003, and none is
added to its private index helper. No published statement or definition is
edited.
