# NYLL M348.003: the inserted family admits substitution

`Langlands.NYLL.LubinTate.SameUniformizer.inVariable_hasSubst` proves the
published target `inVariable_hasSubstStatement (σ := σ) e`, namely
`MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i)`.

It retains `{K : Type u} [Field K]`, `{F : LocalField.{u,v} K}`,
`{π : F.valuationSubring}`, `{σ : Type*}`, the instance `[Finite σ]`,
and the explicit argument `(e : LubinTateSeries F π)`. The field, value group
and variable universes remain independent. No uniformizer hypothesis is
added. The explicit `σ` in the target type preserves the intended variable
type because `e` alone does not determine it.

## Source and attribution

This is M348.003, source lines 46–51, of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its source prerequisite
M348.002 occurs at lines 38–44. The source-file SHA-256 is
`334516024f5516e2303b6db285978e437b43bcfce8e38939c6536b7c46079afb`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the published errata notes.

## Implemented proof and dependencies

Apply `MvPowerSeries.hasSubst_of_constantCoeff_zero` to the family
`i ↦ inVariable e i`. The `[Finite σ]` instance supplies the finiteness
condition, and the private lemma `constantCoeff_inVariable_for_subst`
supplies the zero constant coefficient at each `i`.

That private lemma repeats exactly the source M348.002 proof:
`PowerSeries.constantCoeff_subst_eq_zero` applies to
`MvPowerSeries.constantCoeff_X` and `e.constantCoeff_eq_zero`.
This is the source M348.003 argument with its prerequisite proved locally,
as permitted by Task 6423 while the separate M348.002 proof awaits
publication. The private name does not introduce a second public theorem
named `constantCoeff_inVariable`.

The only direct import is the published sibling `Statements` module;
its dependencies provide the definitions and Mathlib substitution lemmas.
This candidate needs no unpublished proof module.

## Modification record

Extract M348.003 to this focused module, prefix its namespace with
`Langlands.NYLL`, express its type using the published target with explicit
`σ`, and replace the source reference to M348.002 by the documented private
prerequisite. Adapt imports and documentation; retain all source hypotheses.
No published statement or definition is edited. The original copyright and
author header is retained with an explicit modification notice;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain unchanged.
