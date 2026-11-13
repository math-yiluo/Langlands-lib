# Changed Lubin–Tate parameter: M391.001

This module extracts the single definition
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer`.
It takes a chosen local-field package `F : LocalField.{u, v} K`, an element
`π : F.valuationSubring`, and a unit `u : F.valuationSubringˣ`, and returns
the valuation-ring element `(u : F.valuationSubring) * π`.
The field `K : Type u` and its instance `[Field K]` remain implicit, and
the field universe `u` and value-group universe `v` remain independent.
The order of multiplication is the coerced unit followed by `π`.

The declaration has no hypothesis that `π` is a uniformizer. Its upstream
name and retained declaration docstring describe the intended application;
the type is the more general valuation-ring element construction above.
Uniformizer preservation and every subsequent source unit require separate
work and are absent from this extraction.

## Source and exact correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`,
lines 52–57](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean#L52-L57).
Its complete source file has SHA-256
`684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
The readable pinned snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

Source unit `M391.001`,
`LubinTate.standardLubinTateChangedUniformizer`, corresponds exactly to
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer`.
Its parameters, binder explicitness, universe parameters, return type,
coercion, multiplication order, definition body, and declaration docstring
are retained. This is a definition artifact, with no proposition target
or proof in this unit.

## Dependency and modification record

The definition uses the shared
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`
and its `LocalField.valuationSubring` accessor from FM Task 6041
(`a71f9b25-ccde-4742-a4c0-676e2f7875f9`).
It introduces no replacement local-field package, instances, or hypotheses.
The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`,
which supplies the structure, valuation-subring accessor and inherited
valuation-ring operations.

Worker 318 made the following changes from the pinned source:

1. Extracted only M391.001 into the focused
   `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Definitions`
   module, omitting all later declarations.
2. Added the `Langlands.NYLL` prefix to the `LubinTate` namespace and
   the opened `LocalFieldTheory.DiscreteValuationField` namespace.
3. Replaced the twelve upstream imports with the shared LocalField
   definition module named above.
4. Replaced the upstream module documentation about later norm and
   uniformizer results with documentation of this extracted construction;
   added the modification notice in the source header and this paired
   Markdown. The original noncomputable section is retained.

The original 2026 copyright, Apache-2.0 release statement and authorship
header remain intact. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained without modification.

## Verification

The focused import is checked through the project Lean service in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
It requires no upstream norm-subgroup or valuation-topology imports.
