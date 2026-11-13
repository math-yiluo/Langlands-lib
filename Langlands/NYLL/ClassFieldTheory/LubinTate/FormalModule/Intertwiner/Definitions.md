# NYLL M348.001, M348.004 and M348.005: insertion, intertwining and defect

This module adapts exactly the three definitions of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Intertwiner`: the insertion
`inVariable` of a one-variable Lubin–Tate series into a chosen variable, the
literal intertwining predicate `Intertwines`, and its additive `defect`. The
four theorems of the same source module are not part of this unit; they
follow as separate Prop targets and proofs.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`.
The source-file SHA-256 is
`334516024f5516e2303b6db285978e437b43bcfce8e38939c6536b7c46079afb`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence

| Source unit | Original declaration and lines | Adapted declaration (Lean lines) |
| --- | --- | --- |
| M348.001 | `LubinTate.SameUniformizer.inVariable`, 33–36 | `Langlands.NYLL.LubinTate.SameUniformizer.inVariable` (42–45) |
| M348.004 | `LubinTate.SameUniformizer.Intertwines`, 53–58 | `Langlands.NYLL.LubinTate.SameUniformizer.Intertwines` (47–52) |
| M348.005 | `LubinTate.SameUniformizer.defect`, 60–66 | `Langlands.NYLL.LubinTate.SameUniformizer.defect` (54–60) |

The section context of source lines 20–31 is retained: a `noncomputable
section`, universes `u v`, `open LocalFieldTheory.DiscreteValuationField`, and
the section variables

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}
```

Inside `namespace Langlands.NYLL.LubinTate.SameUniformizer`, the opened
namespace resolves to `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
so `LocalField` is the shared published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`
and `LubinTateSeries F π` is the published
`Langlands.NYLL.LubinTate.LubinTateSeries F π`. Thus `K`, `F` and `π` are
implicit, the universes `u` and `v` of the field and value group are
independent, and the variable type `σ` lies in a third, independent universe.
The element `π` is arbitrary in `F.valuationSubring`; no uniformizer
hypothesis is added. No `Fintype` or `Finite` hypothesis is imposed on `σ` in
any of the three definitions, exactly as in the source.

## Mathematical meaning

Write `O = F.valuationSubring` and let `e, ebar : LubinTateSeries F π`, so
their underlying series `e.toPowerSeries`, `ebar.toPowerSeries` lie in
`O⟦X⟧` with zero constant coefficient and linear coefficient `π`.

- **`inVariable e i`** (M348.001), for `i : σ`, is the multivariable series
  `PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries` in
  `MvPowerSeries σ O`, i.e. `e(X_i)`: the one-variable series with its
  variable replaced by the `i`-th variable. Since `X_i` has zero constant
  coefficient, this is a genuine substitution in Mathlib's sense. The
  declaration is noncomputable, as in the source.
- **`Intertwines e ebar H`** (M348.004), for `H : MvPowerSeries σ O`, is the
  proposition
  `PowerSeries.subst H e.toPowerSeries = MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H`,
  i.e. the literal equation `e(H(X)) = H(ebar(X_i))_i` of the source
  docstring. It is a `def` returning `Prop`, a predicate used by later
  units, not a theorem target.
- **`defect e ebar H`** (M348.005) is the difference of the same two sides,
  `PowerSeries.subst H e.toPowerSeries - MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H`,
  in `MvPowerSeries σ O`; it is noncomputable, as in the source.

Both sides use Mathlib's total substitution operations
`PowerSeries.subst` and `MvPowerSeries.subst`
(`Mathlib.RingTheory.PowerSeries.Substitution`,
`Mathlib.RingTheory.MvPowerSeries.Substitution`). These are defined for all
inputs; their algebraic substitution laws are available only under the
corresponding `HasSubst` conditions (nilpotent constant coefficients and,
for a family, finitely many nonzero entries at each coefficient index).
Exactly as in the source, `Intertwines` and `defect` take no `HasSubst`
hypothesis on `H` or on the inserted family; they are literal equations and
differences of the two total expressions. The relation
`Intertwines e ebar H ↔ defect e ebar H = 0` is the separate source theorem
M348.006, not part of this definition unit.

## Dependencies and modification record

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions`,
  the published focused module of M336.001 `LubinTateSeries`, which itself
  imports the shared published `LocalField`
  (`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`);
- `Mathlib.RingTheory.MvPowerSeries.Substitution`, unchanged from the source;
- `Mathlib.RingTheory.PowerSeries.Substitution`, which declares
  `PowerSeries.subst`.

The source imports the whole source modules
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Series` and
`Nyll.ClassFieldTheory.LubinTate.FormalModule.LinearTerm`. None of the three
definitions refers to M347 `linearForm` or `HasLinearTerm` or to the M336.002
extensionality theorem; the source obtains `PowerSeries.subst` only
transitively through LinearTerm's import of
`Mathlib.RingTheory.PowerSeries.Substitution`. That Mathlib module is
therefore imported directly instead, and a focused Lean check of this module
succeeded with these three imports.

The complete adaptations are:

1. extraction of M348.001, M348.004 and M348.005 into this definition-only
   file, omitting the four source theorems M348.002, M348.003, M348.006 and
   M348.007, which are published separately as Prop-valued targets and
   later proofs;
2. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer`;
3. the import replacements described above;
4. a modified-file notice in the header and a module docstring extended to
   mention the insertion.

The noncomputable section, universes, `open`, section variables, the three
declaration docstrings, names, binders, types and bodies are otherwise
unchanged. This source module has no patch10 edits. No coercion, simp
attribute or global instance is introduced.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
