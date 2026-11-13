# NYLL M120: principal-unit graded-piece data

This module preserves the adjacent subquotient wrapper, its canonical group,
the explicit identification with the adjacent subquotient and the source
finite-instance transport. Finiteness remains conditional on the named
subquotient already being finite.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean` (M120).
The original file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.
The readable original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`
under registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Source declaration lines | Adapted declaration |
| --- | --- | --- | --- |
| M120.038 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPiece` | 400–401 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPiece` |
| M120.039 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceGroup` | 407–411 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceGroup` |
| M120.041 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient` | 423–429 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient` |
| M120.042 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceFinite` | 432–437 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitGradedPieceFinite` |

All original docstrings immediately preceding these declarations are retained.
The shared source context is `universe u v` and
`variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)` in
`LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration`.

## Complete telescopes and constructions

All four declarations begin with the implicit carrier `{G : Type u}`,
`[Group G]`, explicit `(U : AntitoneSubgroupFiltration G)` and explicit
`(n : ℕ)`, in that order. The wrapper M120.038 has no additional hypothesis
and returns `Type u`; its body is exactly
`U.principalUnitSubquotient n (n + 1)`.

M120.039 and M120.041 then take
`[(U.principalUnitSubgroup (n + 1)).Normal]`. The former changes its target to
`Group (U.principalUnitSubquotient n (n + 1))` and uses `infer_instance`.
The latter returns a multiplicative equivalence from the graded piece to
that subquotient, with the original proof changing to the reflexive
subquotient equivalence and returning `MulEquiv.refl _`.

M120.042 has the same normality instance followed by
`[Finite (U.principalUnitSubquotient n (n + 1))]`. It remains a
`noncomputable instance`, returning `Finite (U.principalUnitGradedPiece n)`
by the exact source expression
`Finite.of_equiv (U.principalUnitSubquotient n (n + 1))
(U.principalUnitGradedPieceEquivSubquotient n).symm.toEquiv`.
The finite-instance assumption is not removed even though the wrapper is
transparent. The unused source universe declaration `v` is retained.

## Modifications and reuse

Worker 321 added the `Langlands.NYLL` namespace prefix, extracted the four
listed declarations and replaced the source imports by
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient`.
Its dependency chain retains all three original Mathlib imports. A new
module-level comment records these changes. All headers, binder kinds and
orders, bodies, embedded proofs, instance scope and priority, noncomputable
modifier and original docstrings remain unchanged.

The current Library and Mathlib were searched before extraction. The
Mathlib quotient group, `MulEquiv.refl` and `Finite.of_equiv` constructions
are reused directly. The instances retain their source scope under the
prefixed names; no unrelated global instance or unpublished helper is
introduced. In particular, source M120.040 `principalUnitGradedPieceMk` is
not needed for these definitions and is not copied. No source theorem is
needed or replaced by an assumption.

## Attribution and scope

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, Apache-2.0, author Naganori Yamaguchi (assisted by
OpenAI Codex). The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public inventory records no patch10 modification for M120. Worker 321
made the extraction and namespace/import changes described above, without
reusing another worker's draft or compatibility patch.

These are data and source instances with their original embedded proofs.
No cardinality theorem, unconditional finiteness theorem, separate
proposition target or host reciprocity result is asserted by this pair.
