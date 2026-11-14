# The transported canonical uniformizer (M335.019)

This module extracts exactly source unit M335.019, lines 284–289 of Naganori
Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L284-L289)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The declaration
command starts at line 286; lines 284–285 are its docstring. The source
file's SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.
Its header, imports, section variables and opened namespaces (lines 1–38)
and the declarations through line 316 were read directly.

The original is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. No compatibility patch
(including the recorded patch10) changes this source module.

## Declaration

`Langlands.NYLL.LubinTate.standardLocalFieldUniformizer` takes the source
section parameters unchanged:

```
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

Its type is `(standardLocalField K).valuationSubring`, the valuation subring
of the canonical local-field package
`Langlands.NYLL.LubinTate.standardLocalField K`. Its value is

```
standardLocalFieldIntegerEquiv K (chosenIntegerRingUniformizer K)
```

that is, the published chosen irreducible element
`Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer K : 𝒪[K]`
(source M133.004, defined as
`Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[K])`),
transported along the ring equivalence
`Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv K :
𝒪[K] ≃+* (standardLocalField K).valuationSubring` (source M335.005).
That equivalence is the identity on underlying elements of `K`, so the
underlying field element of `standardLocalFieldUniformizer K` is that of
`chosenIntegerRingUniformizer K`; this is the source's M335.020 coercion
equation, which holds by `rfl` and is not part of this unit.

The definition is noncomputable, as in the source. It is data only: that
it is a uniformizer of the package's valuation is the separate Prop target
`standardLocalFieldUniformizer_isUniformizerStatement` (source M335.021),
in the sibling module `UniformizerStatements`.

## Exact source correspondence

| Source unit and declaration | Adapted declaration | Type and body |
| --- | --- | --- |
| M335.019, `LubinTate.standardLocalFieldUniformizer`, lines 284–289 | `Langlands.NYLL.LubinTate.standardLocalFieldUniformizer` | `(standardLocalField K).valuationSubring := standardLocalFieldIntegerEquiv K (chosenIntegerRingUniformizer K)`; docstring, type and body unchanged. |

The source names `standardLocalField`, `standardLocalFieldIntegerEquiv`
and `chosenIntegerRingUniformizer` resolve to the published declarations
`Langlands.NYLL.LubinTate.standardLocalField`,
`Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv` and
`Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer`.

## Imports and scope

The imports are the published modules
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquiv`
(M335.005, which imports the M335.001 package) and
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Definitions`
(M133.004). They replace the six upstream imports: the discrete-valuation
field basics, the principal-unit residue quotient and Teichmüller
decomposition, the finite-extension complete DVF, the whole ideal-quotient
module and the standard open subgroups. No principal-unit or Teichmüller
declaration is used by this unit.

Only M335.019 is extracted. The intervening source declarations
M335.002–.018, the coercion equation M335.020 and the theorem M335.021 are
outside this unit.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file.

Worker 412 made these modifications on 14 November 2026:

- extracted M335.019 and its docstring into this focused module, omitting
  all other source declarations;
- prefixed the declaration namespace `LubinTate` with `Langlands.NYLL`;
- replaced the six upstream imports by the two published imports above;
- of the source's opened namespaces (`LocalFieldTheory`,
  `LocalFieldTheory.DiscreteValuationField`,
  `LocalFieldTheory.DiscreteValuationField.CompleteDVF`,
  `LocalFieldTheory.IsNonarchimedeanLocalField`) and
  `open scoped ValuativeRel`, kept only `open LocalFieldTheory`, which
  resolves inside `Langlands.NYLL.LubinTate` to
  `Langlands.NYLL.LocalFieldTheory` and makes
  `chosenIntegerRingUniformizer` available under its source spelling;
- replaced the module documentation, added the prominent modification
  notice in the Lean header, and wrote this paired Markdown.

The section variables, the `noncomputable section`, the declaration's type
and body and its docstring are otherwise unchanged.
