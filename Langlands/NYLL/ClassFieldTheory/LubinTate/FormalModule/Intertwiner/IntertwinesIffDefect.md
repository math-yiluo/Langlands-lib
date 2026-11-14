# NYLL M348.006: intertwining is vanishing of the defect

`Langlands.NYLL.LubinTate.SameUniformizer.intertwines_iff_defect_eq_zero`
proves the published target
`intertwines_iff_defect_eq_zeroStatement e ebar H`, namely
`Intertwines e ebar H ↔ defect e ebar H = 0`.

The source parameters are preserved: `{K : Type u} [Field K]`,
`{F : LocalField.{u,v} K}`, `{π : F.valuationSubring}`, `{σ : Type*}`,
and explicit `(e ebar : LubinTateSeries F π)`
`(H : MvPowerSeries σ F.valuationSubring)`. The three universes are
independent. There is no finiteness, `HasSubst`, or uniformizer hypothesis.
The definitions use Mathlib's total substitution operations, so this
subtraction identity needs no substitution law.

## Source and attribution

This is M348.006, source lines 68–73, of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source-file SHA-256 is
`334516024f5516e2303b6db285978e437b43bcfce8e38939c6536b7c46079afb`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the published errata notes.

## Implemented proof and dependencies

The proof uses `simp only` to unfold the target, `Intertwines` and `defect`.
Writing the two substituted series as `A` and `B`, the goal is
`(A = B) ↔ (A - B = 0)`. Mathlib's `sub_eq_zero` rewrites the right side to
`A = B`, completing the proof. This is the source proof, with the target
abbrev additionally named in the simplification list.

The only direct import is the published sibling `Statements` module.
Its `Definitions` dependency supplies the two substituted series and their
additive group structure. No other M348 proof is used.

Because the theorem is typed by a reducible target abbrev, downstream
rewriting can use `simp only [intertwines_iff_defect_eq_zero]` or
`.mp`/`.mpr`; a bare `rw [intertwines_iff_defect_eq_zero]` does not unfold
the theorem's target to an equivalence automatically.

## Modification record

Extract the source theorem to this focused module, add the `Langlands.NYLL`
namespace prefix, replace its displayed type by the published target and
unfold that target in the proof. Adapt imports and documentation, retaining
all binders and hypotheses. No published statement or definition is edited.
The original copyright and author header is retained with an explicit
modification notice; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged.
