# Target: the underlying series of the standard Lubin–Tate series

This module states source unit M338.003 as the Prop-valued target
`Langlands.NYLL.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeriesStatement`.
It asserts nothing by itself. The theorem
`Langlands.NYLL.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries`,
with the source `@[simp]` attribute, is to prove it in a separate
`lean.proof@1` successor.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardSeries.lean`,
lines 60–71 (namespace `LubinTateSeries`, docstring, `@[simp]`, theorem
`standardLubinTateSeries_toPowerSeries` at lines 64–69 and
`end LubinTateSeries`), with context at lines 23–32
(noncomputable section, universes, namespace, opened namespace and section
variables). The source-file SHA-256 is
`2184cfbc0ef0b53881fd61f4b227147a9fe77949670c99232d4d2c3c9e9dc5df`.
The readable original is beneath
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

The source theorem reads

```lean
@[simp]
theorem standardLubinTateSeries_toPowerSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTateSeries hπ).toPowerSeries =
      standardLubinTatePowerSeries F π :=
  rfl
```

## Statement

For independent universes `u v`, implicit `K : Type u` with `[Field K]`,
implicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
implicit `π : F.valuationSubring`, and the explicit hypothesis
`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, the target is

  `(standardLubinTateSeries hπ).toPowerSeries = standardLubinTatePowerSeries F π`.

That is, the underlying power series of the standard Lubin–Tate series
`Langlands.NYLL.LubinTate.standardLubinTateSeries hπ` (M338.002) is the
polynomial series `π X + X ^ q` of M338.001,
`Langlands.NYLL.LubinTate.standardLubinTatePowerSeries F π`, with
`q = Nat.card F.residueField`. Both sides are power series over
`F.valuationSubring`. No hypothesis is added or omitted, and the
conclusion is the source equation unchanged.

The target is an `abbrev` returning `Prop`, so it is reducible. A proof
`theorem standardLubinTateSeries_toPowerSeries (hπ) : standardLubinTateSeries_toPowerSeriesStatement hπ`
tagged `@[simp]` therefore yields the same rewrite rule as the source
theorem. A private development check confirmed that, with such a proof,
`simp only [standardLubinTateSeries_toPowerSeries]` rewrites
`(standardLubinTateSeries hπ).toPowerSeries`, which `simp only []` cannot.

## Dependencies and modification record

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.Definitions`
(M338.002, which itself imports M338.001 and the shared `LubinTateSeries`
and `LocalField` modules). It replaces the source import
`Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation`.

The complete adaptations are:

- the source theorem becomes the Prop-valued `abbrev` target named with
  the suffix `Statement`; the theorem name, its `@[simp]` attribute and its
  `rfl` proof are left to the proof successor;
- the `Langlands.NYLL` prefix on the namespace, so the source namespace
  `LubinTate.LubinTateSeries` becomes
  `Langlands.NYLL.LubinTate.LubinTateSeries`; the opened namespace
  `LocalFieldTheory.DiscreteValuationField` is unchanged;
- the focused import described above;
- a modified-file notice, replacement module documentation, and the prefix
  `Target:` in the docstring.

The noncomputable section, universes `u v`, the section variables of
lines 31–32, the hypothesis name and type, and the equation are retained.
This source file has no patch10 edits. The original 2026 copyright,
Apache-2.0 release line and author header are preserved. Existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain unchanged, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No project erratum for this source was found in the current errata notes.
