# NYLL M076.002: `mem_intermediateSubgroup_iff`

## Exact target and implemented proof

For `{G : Type u_1}` with `[Group G]` and `[TopologicalSpace G]`,
`{K : ClosedSubgroup G}`, `L : FiniteGaloisSubextension K`,
`S : Subgroup L.extensionQuotient` and `k : K.toSubgroup`, the theorem
proves exactly `mem_intermediateSubgroup_iffStatement L S k`, namely
`k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S`.

The published definition `intermediateSubgroup L S` is
`S.comap L.extensionQuotientMk`, and membership in `Subgroup.comap f S` is
definitionally membership of `f k` in `S`. The proof is therefore the term
`Iff.rfl`, checked against the statement by definitional unfolding, exactly
as in the source. It uses no theorem beyond `Iff.rfl`.

The full theorem name is
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff`;
its published target is
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iffStatement`.
The only project import is the published statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements`.

Source unit M076.002 is the theorem at lines 51–55, preceded by
`omit [IsTopologicalGroup G] in` (line 47), its docstring (lines 48–49) and
`@[simp]` (line 50). The port keeps the docstring and drops the `@[simp]`
attribute: the type is now the Prop-valued statement constant, whose head is
not an `Iff`, so the attribute would not serve as the source simp lemma.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
(SHA-256 `f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`).
The readable pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 751 extracted this one theorem, prefixed the source namespace
`ClassFormation` with `Langlands.NYLL`, replaced the broad source module
import by the focused published imports listed above, dropped the unused
`open KummerTheory`, and wrote the theorem's type as the corresponding
published `Statement` applied to the original parameters. The source section
`variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
together with the source line `omit [IsTopologicalGroup G] in` is rendered
as the section `variable {G : Type*} [Group G] [TopologicalSpace G]`, and
the source section variable `{K : ClosedSubgroup G}` is written as the
theorem's first binder, matching the published statement's telescope. The
original copyright and author header is retained. See
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. The implementation
changes specific to this theorem are described above. No imported Lean or
Markdown file is modified.

This is an abstract subgroup result. It supplies no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity theorem.
