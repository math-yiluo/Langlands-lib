# Canonical integer-unit equivalence (M335.011)

For `K : Type` with `[Field K] [ValuativeRel K] [TopologicalSpace K]`
and `[IsNonarchimedeanLocalField K]`, the definition
`Langlands.NYLL.LubinTate.standardLocalFieldIntegerUnitsEquiv K` has type
`𝒪[K]ˣ ≃* (standardLocalField K).valuationSubringˣ`.
Its body is exactly
`Units.mapEquiv (standardLocalFieldIntegerEquiv K).toMulEquiv`:
it applies Mathlib's functorial equivalence on units to the underlying
multiplicative equivalence of the canonical integer-ring equivalence.

## Source and attribution

This extracts M335.011, starting at line 166 and ending at line 170, from
Naganori Yamaguchi's ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source path
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`.
The source file SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.
The surrounding section parameters are at lines 37–38, and the extracted
documentation starts at line 164. Registered sources are
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`. The readable pinned source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The Lean file preserves the original 2026 copyright, Apache-2.0 license and
author header. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged and byte-identical to the pinned files.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Adaptation

The source namespace `LubinTate` becomes `Langlands.NYLL.LubinTate`.
The source spelling, Type-level field parameter, four instance hypotheses,
result type, noncomputable declaration, documentation and construction are
preserved. Only line wrapping changes within the definition.

The original six whole-module NYLL imports are replaced by
`Mathlib.Algebra.Group.Units.Equiv` and the focused published module exporting
`Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv`. The latter supplies
`standardLocalField` and FM's shared
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField` through
its imports. The four unused source `open` commands are omitted; the scoped
`ValuativeRel` notation and noncomputable section are retained. The module
introduction is narrowed to this definition. No API or mathematical body is
changed, and no patch10 edit applies to this source unit.

## Dependencies and environment

The focused published NYLL import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquiv`.
It exports `Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv` and imports
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Definitions`,
which exports the canonical `standardLocalField` on FM's shared `LocalField`
package. These declarations are reused without alteration. Mathlib's
`Mathlib.Algebra.Group.Units.Equiv` supplies `Units.mapEquiv`.

The approved compilation environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Upstream used Lean 4.35.0-rc2.
This unit contains only M335.011; it adds no coercion target or theorem proof.
