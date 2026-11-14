# NYLL M348.007: each coordinate intertwines a series with itself

`Langlands.NYLL.LubinTate.SameUniformizer.intertwines_X` proves the
published target `intertwines_XStatement e i`, namely
`Intertwines e e (MvPowerSeries.X i)`.

It retains `{K : Type u} [Field K]`, `{F : LocalField.{u,v} K}`,
`{π : F.valuationSubring}`, `{σ : Type*}`, the instance `[Finite σ]`,
and explicit `(e : LubinTateSeries F π) (i : σ)`. The field, value group
and variable universes remain independent, and no uniformizer hypothesis
is added.

## Source and attribution

This is M348.007, source lines 75–81, of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its prerequisites
M348.002 and M348.003 occur at lines 38–44 and 46–51. The source-file
SHA-256 is `334516024f5516e2303b6db285978e437b43bcfce8e38939c6536b7c46079afb`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the published errata notes.

## Implemented proof and dependencies

First unfold the target abbrev and `Intertwines`. The equation becomes

```lean
PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries =
  MvPowerSeries.subst (fun j : σ ↦ inVariable e j) (MvPowerSeries.X i)
```

Apply `MvPowerSeries.subst_X` with the substitution condition established
by the private lemma `inVariable_hasSubst_for_coordinate`. The right side
reduces to `inVariable e i`, whose definition is the left side, so `rfl`
closes the goal.

The private substitution lemma applies
`MvPowerSeries.hasSubst_of_constantCoeff_zero` under `[Finite σ]`.
Its private prerequisite `constantCoeff_inVariable_for_coordinate`
uses `PowerSeries.constantCoeff_subst_eq_zero`,
`MvPowerSeries.constantCoeff_X`, and `e.constantCoeff_eq_zero`.
These repeat exactly the source M348.003 and M348.002 arguments under fresh
private names, as permitted by Task 6423 while those focused proofs await
publication. They introduce no duplicate public adapted theorem names.

The only direct import is the published sibling `Statements` module.
Its dependencies supply the definitions and Mathlib substitution laws;
no unpublished proof module is needed.

## Modification record

Extract M348.007 to this focused module, prefix the namespace with
`Langlands.NYLL`, state its type using the published target and explicitly
unfold that target before the source rewriting argument. Prove the two
prerequisites privately as documented above. Adapt imports and documentation
while retaining all source hypotheses. No published statement or definition
is edited. The original copyright and author header is retained with an
explicit modification notice; `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged.
