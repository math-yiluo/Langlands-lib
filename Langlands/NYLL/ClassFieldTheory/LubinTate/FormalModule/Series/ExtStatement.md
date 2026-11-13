# Extensionality target for Lubin–Tate series

This module publishes the proposition-valued target
`Langlands.NYLL.LubinTate.LubinTateSeries.extStatement` for source unit
M336.002. It states that two packages with equal underlying power series
are equal. It supplies no proof.

## Original source and exact telescope

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Series.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Series.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 63–69,
with the universe and variable context at lines 25–30 and 59.
The file's SHA-256 is
`78e883128e132584b700e3518c794774db5c458ea9a31a735519857b6204e3e9`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
and `nyll-classfieldtheory-fbd320cd-supplement`; the readable file is under
the pinned snapshot root specified in [Definitions.md](Definitions.md).

The source theorem name `LubinTate.LubinTateSeries.ext` corresponds to
the future proof name `Langlands.NYLL.LubinTate.LubinTateSeries.ext`.
The published target adds the suffix `Statement` and retains this telescope:

```lean
{K : Type u} [Field K]
{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K}
{π : F.valuationSubring}
{e e' : Langlands.NYLL.LubinTate.LubinTateSeries F π}
(h : e.toPowerSeries = e'.toPowerSeries)
```

The body is the proposition `e = e'`. The hypothesis `h` is an explicit
argument of the target even though its value is not used in the target's
body. Thus the exact source implication is retained in the declaration
type: applying this target requires the source hypothesis. The field
universe `u` and value-group universe `v` remain independent. Both
packages share the same chosen `F` and `π`, and no uniformizer assumption
or other hypothesis is added.

## Dependencies and modification record

The sole direct import is the focused
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions`
module. Its published structure and the same shared `LocalField`
accessors are reused without modification.

The complete adaptations are extraction of only the M336.002 theorem
type into a focused statement file; the `Langlands.NYLL` namespace prefix;
renaming `ext` to `extStatement`; replacing the theorem and proof by a
`def` returning `Prop`; replacing the original imports by the focused
definition import; adding the modified-file notice, target docstring and
module documentation; and suppressing the unused-variable linter only
on this declaration to retain the source hypothesis name `h`.
The source section context, independent universes and binder kinds are
preserved. The original `@[ext]` attribute is deferred to the separate
proof theorem, because this file defines a proposition. No source
proof or extra result is included. This source file has no patch10 edits.

The original 2026 copyright, Apache-2.0 release line and author header
are preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No project erratum for this source was found in the current errata notes.
