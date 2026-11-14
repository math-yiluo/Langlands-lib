# Canonical local-field package of a nonarchimedean local field (M335.001)

This module extracts exactly source unit M335.001,
`LubinTate.standardLocalField`, from Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L40-L46)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`: docstring lines
40–41 and declaration lines 42–46. Its context is the header (lines 1–5),
`noncomputable section` (line 26), `open scoped ValuativeRel` (line 28),
`namespace LubinTate` (line 30), the opens at lines 32–35 and the section
variables at lines 37–38. The source file's SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.

The original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. The project errata notes
contain no entry for either source, and the recorded patch10 does not
change this source module.

## The definition

`Langlands.NYLL.LubinTate.standardLocalField` takes the source section
variables in source order, all explicit or instance binders exactly as in
lines 37–38:

```
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

Here `IsNonarchimedeanLocalField` is Mathlib's class of nonarchimedean
local fields: the topology of `K` is the valuative topology of the given
`ValuativeRel`, `K` is locally compact and the valuation is nontrivial.
The field remains in `Type` (universe 0), as in the source; no universe is
generalized.

Its type is the shared FM package
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField K`, written
`LocalField K` as in the source. Since the parent package
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF K` has type
`CompleteDVF.{0, 0} K` for `K : Type`, the universe arguments are
inferred as `LocalField.{0, 0} K`; the definition has no universe
parameters. The noncomputable definition is the structure instance with
two fields:

- `toCompleteDVF := LocalFieldTheory.localCompleteDVF K`, which resolves to
  the published `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K`: the
  canonical complete discrete valuation of `K`, whose valuation is Mathlib's
  `Valued.v` for the uniformity `IsTopologicalAddGroup.rightUniformSpace K`.
- `residueFinite`, the proof that the residue field of this parent package
  is finite. As in the source, the tactic proof
  `change Finite 𝓀[K]; infer_instance` uses `change` to restate the goal
  for Mathlib's topology-first residue field `𝓀[K]`, which is the scoped
  notation `IsLocalRing.ResidueField ↥𝒪[K]` with
  `𝒪[K] = Valuation.integer (ValuativeRel.valuation K)`. The `change` step
  checks that the residue field of the package is definitionally this type.
  The instance found is Mathlib's `Finite 𝓀[K]` instance for nonarchimedean
  local fields, declared in `Mathlib.NumberTheory.LocalField.Basic`.

The structure retains the instance attribute of `LocalField.residueFinite`,
so the resulting finiteness is available to typeclass inference for
`(standardLocalField K).residueField`. The definition packages the
existing canonical data; it chooses no further valuation, uniformizer or
residue data.

The three source comparison theorems that follow (M335.002–004: forgetting
to `localCompleteDVF K`, equality of the valuation with
`ValuativeRel.valuation K`, and the cardinality of the residue field) are
not part of this unit. They are stated as the separate proposition targets
in the sibling module `Statements` of this directory and are not proved
here.

## Exact source correspondence

| Source unit and declaration | Adapted declaration | Type and body |
| --- | --- | --- |
| M335.001, `LubinTate.standardLocalField`, lines 40–46 | `Langlands.NYLL.LubinTate.standardLocalField` | `LocalField K`, with `toCompleteDVF := LocalFieldTheory.localCompleteDVF K` and `residueFinite` by `change Finite 𝓀[K]; infer_instance`; binders, body and docstring verbatim. |

The source names `LocalField` and `LocalFieldTheory.localCompleteDVF`
resolve, in the source, to `LocalFieldTheory.DiscreteValuationField.LocalField`
(NYLL M334.001) and `LocalFieldTheory.localCompleteDVF` (NYLL M248.001). In
this module they resolve to their published adaptations
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField` and
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF`, because the surrounding
namespace is `Langlands.NYLL.LubinTate`.

## Imports

The six source imports (the NYLL modules
`LocalField.DiscreteValuationField.Basic`, its `PrincipalUnits.ResidueQuotient`
and `PrincipalUnits.TeichmullerDecomposition`, and the
`NonarchimedeanLocalField` modules `FiniteExtensionCompleteDVF`,
`IdealQuotients` and `StandardOpenSubgroups`) are replaced by two focused
published modules:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`,
  which supplies `LocalField` and its residue-field accessor;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`,
  which supplies `localCompleteDVF` and imports
  `Mathlib.NumberTheory.LocalField.Basic`, the source of
  `IsNonarchimedeanLocalField`, the notation `𝓀[K]` and the `Finite 𝓀[K]`
  instance.

The principal-unit, Teichmüller, ideal-quotient and open-subgroup APIs are
used only by the later units M335.005–021 and are not imported. A
successful development check of this module in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled it with no errors or
warnings; the upstream file was built with Lean 4.35.0-rc2.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file.

Worker 409 made these modifications on 14 November 2026:

- extracted only M335.001 with its docstring into this focused module,
  omitting the comparison theorems M335.002–004 (stated separately as
  targets) and all later source declarations M335.005–021;
- changed the namespace `LubinTate` to `Langlands.NYLL.LubinTate`;
- replaced the six source imports by the two published imports above;
- kept, of the four source opens at lines 32–35, only
  `open LocalFieldTheory.DiscreteValuationField`, which this unit uses for
  `LocalField`; `open LocalFieldTheory`,
  `open LocalFieldTheory.DiscreteValuationField.CompleteDVF` and
  `open LocalFieldTheory.IsNonarchimedeanLocalField` serve only later
  units and are omitted; `open scoped ValuativeRel` is retained;
- replaced the module documentation, which also described the later
  integer-ring and principal-unit identifications, by documentation of
  this unit only, added the prominent modification notice in the Lean
  header, and wrote this paired Markdown.

The section variables, the declaration's name suffix, type, body, tactic
proof and docstring are unchanged. No compatibility patch is needed.
