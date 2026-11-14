# NYLL M348.002: the inserted series has zero constant coefficient

`Langlands.NYLL.LubinTate.SameUniformizer.constantCoeff_inVariable` proves
the published target `constantCoeff_inVariableStatement e i`, namely
`MvPowerSeries.constantCoeff (inVariable e i) = 0`. It retains the source
`@[simp]` attribute.

The parameters are `{K : Type u} [Field K]`, `{F : LocalField.{u,v} K}`,
`{π : F.valuationSubring}`, `{σ : Type*}`, and explicit
`(e : LubinTateSeries F π) (i : σ)`. The field, value group and variable
universes remain independent. Neither finiteness of `σ` nor a uniformizer
hypothesis on `π` is required.

## Source and attribution

This is M348.002, source lines 38–44, of Naganori Yamaguchi's
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

The proof is the source proof unchanged. The reducible target unfolds to the
constant coefficient of `PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries`.
Apply `PowerSeries.constantCoeff_subst_eq_zero`, using
`MvPowerSeries.constantCoeff_X` for the inserted series and
`e.constantCoeff_eq_zero` for the Lubin–Tate series. These are exactly the
two zero constant coefficients needed by that Mathlib theorem.

The only direct import is the published sibling `Statements` module. Its
`Definitions` dependency supplies `inVariable`, the shared `LubinTateSeries`
and `LocalField`, and Mathlib's power-series substitution results. No other
M348 proof is needed.

## Modification record

The source theorem is extracted to this focused module, its namespace gains
`Langlands.NYLL`, and its type is expressed through the already published
`constantCoeff_inVariableStatement` abbrev. The original proof, section
parameters and `@[simp]` attribute are preserved. Imports and documentation
are adapted to the focused Library modules. No published statement or
definition is edited. The original copyright and author header is retained,
with an explicit modification notice; `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged.
