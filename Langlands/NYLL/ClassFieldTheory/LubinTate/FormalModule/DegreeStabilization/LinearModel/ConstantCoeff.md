# NYLL M351.012: the linear model has zero constant coefficient

This module proves the published proposition
`Langlands.NYLL.PortInternal.M351.d012Statement` under the prescribed name
`Langlands.NYLL.PortInternal.M351.d012`. For
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {σ : Type w}`,
the explicit arguments are `(π : F.valuationSubring) (i : σ)`, and the
conclusion is exactly `d012Statement π i`, that is,

```lean
MvPowerSeries.constantCoeff (d011 π i) = 0
```

Here `d011 π i = MvPowerSeries.C π * MvPowerSeries.X i`. The variable
type is arbitrary, with no `Finite` or `Fintype` assumption; `π` is any
element of the valuation subring, with no uniformizer assumption. The
universes of the field, value group, and variable type remain independent.
`LocalField` is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.

## Original source and correspondence

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
lines 405–413: the source-private theorem
`LubinTate.SameUniformizer.linearInVariableStabilization_constantCoeff`.
This is inventory unit M351.012. Its source-private linear model,
defined at lines 400–403, is already published as
`Langlands.NYLL.PortInternal.M351.d011`.

The readable pinned original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
Its verified SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The registered sources are
`external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No NYLL-specific errata file was found in the Library's `notes/errata/`.

## Implemented proof and dependencies

The single direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements`.
It supplies the published target and, through its imports, `d011`,
`LocalField`, the valuation subring, and Mathlib's multivariable power
series operations. The proof uses no other NYLL proof theorem.

The proof first exposes the equation underlying the reducible target with
`show`. It then unfolds `d011` and uses `map_mul` for the ring homomorphism
`MvPowerSeries.constantCoeff`. The lemma
`MvPowerSeries.constantCoeff_C` evaluates the first factor to `π`.
Rewriting the other factor with
`← MvPowerSeries.coeff_zero_eq_constantCoeff_apply` and
`MvPowerSeries.coeff_zero_X` evaluates it to zero; `mul_zero` closes the
goal. These multivariable power series lemmas are in
`Mathlib.RingTheory.MvPowerSeries.Basic`, available transitively.
This is the original source rewrite chain, with `d011` substituted for
`linearInVariableStabilization`.

## Modifications and attribution

Worker 790, 16 November 2026:

1. Extract only M351.012 and expose the source-private theorem under the
   prescribed public internal name `Langlands.NYLL.PortInternal.M351.d012`.
2. State its result as the already published `d012Statement π i`, then
   expose the source equation with `show` before the unchanged rewrite chain.
3. Use the published name `d011` for the source-private linear model and
   qualify the opened local-field namespace with `Langlands.NYLL`.
4. Replace the source imports by the focused published statement import.
   Omit the unused section `[Fintype σ]` and the associated `omit` command;
   the source explicitly omits that instance for this theorem.
5. Omit unrelated source declarations, the unused `noncomputable section`,
   `open scoped BigOperators`, and local `Classical.propDecidable` instance.
   Add module and declaration documentation and this modification record.

The original copyright, Apache-2.0 release line, and author header are
preserved verbatim. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged; their verified SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.
