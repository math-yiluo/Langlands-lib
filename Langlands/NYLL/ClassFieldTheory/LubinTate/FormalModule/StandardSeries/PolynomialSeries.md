# The standard Lubin–Tate polynomial series

This module adapts exactly source unit M338.001, the definition
`Langlands.NYLL.LubinTate.standardLubinTatePowerSeries`. For a local
field package `F` and an element `π` of its valuation subring, it is the
one-variable formal power series

  `π X + X ^ q`,  where `q = Nat.card F.residueField`,

with coefficients in `F.valuationSubring`. It is a plain definition: it
asserts nothing and needs no uniformizer hypothesis. The packaging of this
series as a Lubin–Tate series for a uniformizer (M338.002) and the
projection law (M338.003) are separate units.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardSeries.lean`,
lines 34–40 (docstring and definition), with context at lines 23–31
(noncomputable section, universes, namespace, opened namespace and the
`K` section variables). The source-file SHA-256 is
`2184cfbc0ef0b53881fd61f4b227147a9fe77949670c99232d4d2c3c9e9dc5df`.
The readable original is beneath
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

The source definition reads

```lean
noncomputable def standardLubinTatePowerSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  PowerSeries.C π * PowerSeries.X +
    PowerSeries.X ^ Nat.card F.residueField
```

and the adapted definition has the same text.

## Parameters and meaning

The declaration retains independent universes `u v`, the implicit
`K : Type u`, the instance `[Field K]`, the explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`
and the explicit `π : F.valuationSubring`. Its type is
`PowerSeries F.valuationSubring`. The `LocalField` is the shared
published extension of `CompleteDVF` by residue-field finiteness; its
`valuationSubring` and `residueField` are that package's existing
accessors.

The body is `PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card F.residueField`:
the constant power series `π` times the variable, plus the variable raised
to the natural cardinality of the residue field. The element `π` is
arbitrary here; no uniformizer condition on `π` is imposed or implied.

## Dependencies and modification record

The direct imports are `Mathlib.SetTheory.Cardinal.Finite` (for
`Nat.card`), `Mathlib.RingTheory.PowerSeries.Basic` (for `PowerSeries`,
`PowerSeries.C` and `PowerSeries.X`), and the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`
(for `LocalField` and its accessors). They replace the source import
`Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation`, none
of whose theorems this definition uses.

The complete adaptations are:

- extraction of M338.001 alone into this definition-only module;
- the `Langlands.NYLL` prefix on the namespace `LubinTate`, so the source
  name `LubinTate.standardLubinTatePowerSeries` becomes
  `Langlands.NYLL.LubinTate.standardLubinTatePowerSeries`; the opened
  namespace `LocalFieldTheory.DiscreteValuationField` is unchanged and
  resolves to the shared `Langlands.NYLL` package inside the new namespace;
- the focused imports described above;
- omission of the source section variables
  `{F : LocalField.{u, v} K} {π : F.valuationSubring}` of line 32, which
  this definition shadows by its own explicit `F` and `π` and therefore
  never uses; they are not part of its signature in the source either;
- a modified-file notice and replacement module documentation.

The noncomputable section, universes `u v`, the variables
`{K : Type u} [Field K]`, the definition's docstring, name, explicit
parameters, type and body are retained. This source file has no patch10
edits. The original 2026 copyright, Apache-2.0 release line and author
header are preserved. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No project erratum for this source was found in the current errata notes.
