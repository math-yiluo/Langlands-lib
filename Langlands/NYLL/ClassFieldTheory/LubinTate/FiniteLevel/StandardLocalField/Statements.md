# Comparison targets for the canonical local-field package (M335.002–004)

This module states, as proposition targets, the three comparison theorems
M335.002–004 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L48-L72)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 48–72. Their
context is the header (lines 1–5), `noncomputable section` (line 26),
`open scoped ValuativeRel` (line 28), `namespace LubinTate` (line 30), the
opens at lines 32–35 and the section variables at lines 37–38. The source
file's SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.

The original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. The project errata notes
contain no entry for either source, and the recorded patch10 does not
change this source module.

## Parameters

Each target is a `def` returning `Prop` in the namespace
`Langlands.NYLL.LubinTate`. Each takes exactly the source section variables,
in source order and with the source binders:

```
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

The source theorems have no further hypotheses, and none is added. The
field remains in `Type`, so the targets have no universe parameters.
`standardLocalField K : LocalField.{0, 0} K` is the M335.001 package of
the sibling module `Definitions`: the canonical complete
discrete valuation `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K`
with the finiteness of its residue field.

## The targets

- `standardLocalField_toCompleteDVFStatement K` (M335.002) is
  `(standardLocalField K).toCompleteDVF = LocalFieldTheory.localCompleteDVF K`,
  an equation in
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{0, 0} K`:
  forgetting the residue-finiteness field of the package gives back the
  published canonical complete DVF.
- `standardLocalField_valuation_eqStatement K` (M335.003) is
  `(standardLocalField K).valuation = ValuativeRel.valuation K`. The left
  side is the valuation field of the parent `CompleteDVF`, of type
  `Valuation K (standardLocalField K).ValueGroup`; the right side is
  Mathlib's canonical valuation of the valuative relation, of type
  `Valuation K (ValuativeRel.ValueGroupWithZero K)`. As in the source,
  the equation typechecks because the two value groups and their ordered
  structures agree after definitional unfolding of `standardLocalField`
  and `localCompleteDVF`.
- `standardLocalField_residueField_natCardStatement K` (M335.004) is
  `Nat.card (standardLocalField K).residueField = Nat.card 𝓀[K]`. Here
  `(standardLocalField K).residueField` is the residue-field accessor
  `LocalField.residueField` of the shared package, and `𝓀[K]` is Mathlib's
  scoped `ValuativeRel` notation for the topology-first residue field
  `IsLocalRing.ResidueField ↥𝒪[K]`, with
  `𝒪[K] = Valuation.integer (ValuativeRel.valuation K)`.

These are statements only: this module supplies no proofs and does not
establish any of the three equalities. The source proves them by `rfl`
(M335.002 and M335.004) and by unfolding `standardLocalField`,
`localCompleteDVF` and `completeDVFOfCompleteValuedField` followed by
`rfl` (M335.003); those proofs belong to later proof tasks.

## Exact source correspondence

| Source unit and declaration | Adapted target | Statement |
| --- | --- | --- |
| M335.002, `LubinTate.standardLocalField_toCompleteDVF`, lines 48–54 (statement 51–53) | `Langlands.NYLL.LubinTate.standardLocalField_toCompleteDVFStatement` | `(standardLocalField K).toCompleteDVF = LocalFieldTheory.localCompleteDVF K` |
| M335.003, `LubinTate.standardLocalField_valuation_eq`, lines 56–64 (statement 58–60) | `Langlands.NYLL.LubinTate.standardLocalField_valuation_eqStatement` | `(standardLocalField K).valuation = ValuativeRel.valuation K` |
| M335.004, `LubinTate.standardLocalField_residueField_natCard`, lines 66–72 (statement 69–71) | `Langlands.NYLL.LubinTate.standardLocalField_residueField_natCardStatement` | `Nat.card (standardLocalField K).residueField = Nat.card 𝓀[K]` |

The proposition bodies are the source theorem types verbatim, and the
docstrings are the source docstrings. The source names
`standardLocalField` and `LocalFieldTheory.localCompleteDVF` resolve to
`Langlands.NYLL.LubinTate.standardLocalField` and the published
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF`, because the
surrounding namespace is `Langlands.NYLL.LubinTate`.
`ValuativeRel.valuation`, `Nat.card` and `𝓀[K]` are the unchanged
Mathlib names.

## Imports

The sole import is the M335.001 module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Definitions`.
Through it come the shared `LocalField` package, the published
`localCompleteDVF` and `Mathlib.NumberTheory.LocalField.Basic`, which
supplies `IsNonarchimedeanLocalField`, `ValuativeRel.valuation` and the
notation `𝓀[K]`. The six source imports, including the principal-unit,
Teichmüller, ideal-quotient and open-subgroup APIs used only by later
units, are not imported. Development checks in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no
errors or warnings, and inspection of each of the three declarations
reported a definition whose type is a proposition. The upstream file was
built with Lean 4.35.0-rc2.

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

- extracted only the statements of M335.002–004 with their docstrings into
  this focused module, omitting M335.001 (in the sibling `Definitions`
  module) and all later source declarations M335.005–021;
- changed the namespace `LubinTate` to `Langlands.NYLL.LubinTate`;
- replaced each `theorem name : P := proof` by a proposition definition
  `def nameStatement : Prop := P` with the same section parameters, adding
  only the suffix `Statement` to the source name;
- omitted the three proofs and the `@[simp]` attributes of M335.002 and
  M335.004, since a proposition definition is not a simp lemma;
- replaced the six source imports by the one import above;
- kept, of the four source opens at lines 32–35, only
  `open LocalFieldTheory.DiscreteValuationField`; the other three serve
  only later units and are omitted; `open scoped ValuativeRel` is retained;
- replaced the module documentation by documentation of these targets,
  added the prominent modification notice in the Lean header, and wrote
  this paired Markdown.

No hypothesis, instance, binder or proposition body is changed beyond the
qualification of names to the published namespace. No compatibility patch
is needed.
