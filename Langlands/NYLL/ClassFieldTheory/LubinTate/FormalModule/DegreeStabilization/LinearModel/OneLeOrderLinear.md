# NYLL M351.015: the linear model has order at least one

This module proves the published proposition
`Langlands.NYLL.PortInternal.M351.d015Statement` as the theorem
`Langlands.NYLL.PortInternal.M351.d015`. For an arbitrary element `π` of
the valuation subring of a local field and a variable `i : σ`, it states

```lean
(1 : ℕ∞) ≤ (Langlands.NYLL.PortInternal.M351.d011 π i).order
```

Here `d011 π i = MvPowerSeries.C π * MvPowerSeries.X i`. The field,
value-group, and variable universes remain independent. The theorem has
exactly the target's parameters
`{K : Type u} [Field K] {F : LocalField.{u, v} K} {σ : Type w}`
followed by `(π : F.valuationSubring) (i : σ)`. It needs no finiteness
assumption on `σ` and no uniformizer or nonzero assumption on `π`. When
`π = 0`, the model is the zero series, whose order is `⊤`, so the same
lower bound still holds.

## Source and attribution

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`, pinned source](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`:

- M351.015, lines 430–435, the source-private theorem
  `LubinTate.SameUniformizer.one_le_order_linearInVariableStabilization`;
- M351.012, lines 405–413, its source-private constant-coefficient input
  `LubinTate.SameUniformizer.linearInVariableStabilization_constantCoeff`.

The source-file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The readable original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the project's `notes/errata/`.

## Implemented proof

The proof follows the original route. A private helper,
`constantCoeff_linearModel_for_order`, unfolds the published linear model
`d011` and uses `map_mul` to take the constant coefficient of the product.
It evaluates the constant coefficient of `C π` by
`MvPowerSeries.constantCoeff_C`, rewrites the constant coefficient of
`X i` as its coefficient at exponent zero, and evaluates that coefficient
using `MvPowerSeries.coeff_zero_X`. The resulting product is zero by
`mul_zero`.

The theorem `d015` applies
`MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr` to this equation.
Mathlib's order is the least total degree of a nonzero coefficient, with
value `⊤` for the zero series. Thus the vanishing constant coefficient
gives precisely the asserted lower bound.

The sibling theorem `Langlands.NYLL.PortInternal.M351.d012` was absent
from this workspace's Library base
`26a5c21c0dd926a6ba1106b5c4a08f30fdea612c`. As authorized by Task 6852,
this module retains the needed calculation privately under a distinct
name. It introduces no declaration under the sibling's reserved name
and makes no separate claim to publishing M351.012.

## Dependencies and modifications

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements`.
That module supplies the exact target, the published model `d011`,
the local-field types, and Mathlib's multivariable power-series order
and coefficient API through its imports. Neither the published
statement/definition pair nor their dependencies are edited.

Worker 793 made these adaptations on 16 November 2026:

1. Rename the source-private M351.015 theorem to the prescribed public
   internal name `Langlands.NYLL.PortInternal.M351.d015`, with result type
   `d015Statement π i`.
2. Replace `linearInVariableStabilization` by the published definition
   `d011`, and give the local M351.012 calculation a distinct private name.
3. Replace the original source imports by the focused published statement
   import and qualify the local-field namespace with `Langlands.NYLL`.
4. Preserve the source's elaborated binders; omit unused source section
   settings and the section `[Fintype σ]`, which both source theorems
   explicitly omit.
5. Add module/declaration documentation and the explicit modification
   record in the Lean header.

The original copyright, Apache-2.0 release line, and author header are
preserved. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
