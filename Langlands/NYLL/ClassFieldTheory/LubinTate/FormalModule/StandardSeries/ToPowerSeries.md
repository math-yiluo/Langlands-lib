# The underlying series of the standard Lubin–Tate series

This module proves the published target
`Langlands.NYLL.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeriesStatement`
with the source-adapted theorem
`Langlands.NYLL.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries`.
The theorem retains the source `@[simp]` attribute.

For independent universes `u v`, implicit `K : Type u` with `[Field K]`,
implicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
implicit `π : F.valuationSubring`, and the explicit hypothesis
`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, it proves

```lean
(standardLubinTateSeries hπ).toPowerSeries =
  standardLubinTatePowerSeries F π
```

Both sides lie in `PowerSeries F.valuationSubring`. The right side is
`PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card F.residueField`.
No hypothesis is added or omitted.

## Implemented proof and dependencies

The entire proof is `rfl`, as in the original. Unfolding the target `abbrev`
exposes the displayed equality. The published definition
`Langlands.NYLL.LubinTate.standardLubinTateSeries` sets its data field
`toPowerSeries := standardLubinTatePowerSeries F π`. Reducing that structure
projection therefore makes both sides definitionally equal, and equality
reflexivity closes the target. The uniformizer hypothesis supplies the
parameter of the packaged series; the projection computation requires no
additional lemma.

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.ToPowerSeriesStatement`.
It transitively supplies the packaged series definition (M338.002), the
polynomial series definition (M338.001), the shared `LubinTateSeries`
structure (M336.001), and the shared `LocalField` package and its Mathlib
dependencies. The proof uses the target and the defining data projection;
it invokes no separate NYLL theorem. No published statement, definition or
dependency is modified.

Because the target is a reducible `abbrev`, the theorem's `@[simp]`
attribute registers the displayed equality as the source rewrite rule.
Its type is precisely `standardLubinTateSeries_toPowerSeriesStatement hπ`.

## Source correspondence and modification record

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardSeries.lean`,
lines 60–71 (M338.003; theorem at lines 64–69), with section context at
lines 23–32 and the defining data field at lines 43–46.
The source file has SHA-256
`2184cfbc0ef0b53881fd61f4b227147a9fe77949670c99232d4d2c3c9e9dc5df`.
Its readable root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
and `nyll-classfieldtheory-fbd320cd-supplement`.

The adaptations are:

- extract only the projection theorem into this focused proof module;
- prefix the source namespace `LubinTate.LubinTateSeries` with
  `Langlands.NYLL`;
- replace the source `Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation`
  import with the focused published target module;
- state the conclusion through the published target `abbrev`, which
  unfolds to the unchanged source equation;
- add the modified-file notice and replace the module documentation.

The original noncomputable section, independent universes, section
variables, opened namespace, theorem name, docstring, `@[simp]` attribute,
uniformizer hypothesis and `rfl` proof are retained. This source file has
no patch10 edits. The published M338.002 definition locally adapts one
proof field, as its own Markdown records; its data field remains the
source expression, so this projection proof is unchanged.

The original 2026 copyright, Apache-2.0 release line and author header
are preserved. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained unchanged, with respective SHA-256
values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The current project errata search found no matching NYLL source erratum.
