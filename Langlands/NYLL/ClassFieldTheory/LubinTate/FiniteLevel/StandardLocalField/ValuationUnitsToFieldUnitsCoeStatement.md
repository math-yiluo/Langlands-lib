# Coercion target for the canonical valuation-unit inclusion

This module states source unit M335.016 as the Prop-valued definition
`Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits_apply_coeStatement`.
It contains no proof.

For a field `K : Type` with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`
and a unit `u : (standardLocalField K).valuationSubringˣ` of the valuation ring
of the canonical local-field package, the proposition is

```lean
((standardLocalFieldValuationUnitsToFieldUnits K u : Kˣ) : K) =
  (((u : (standardLocalField K).valuationSubringˣ) :
    (standardLocalField K).valuationSubring) : K)
```

That is: the element of `K` underlying the field unit
`standardLocalFieldValuationUnitsToFieldUnits K u` (M335.015) equals the
element of `K` underlying `u`, obtained by coercing the unit to the
valuation ring and the valuation-ring element to `K`. The statement asserts
nothing about other maps, the principal-unit filtration or any image subgroup.

The definition's parameters are exactly the source's: the section variables
`(K : Type)` and its four instance arguments, followed by the source theorem's
explicit argument `(u : (standardLocalField K).valuationSubringˣ)`. The
statement returns `Prop`.

## Source and correspondence

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean>),
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The full source file has SHA-256
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`. The source
registrations are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

| Source unit and name | Source lines | Adapted declaration |
| --- | --- | --- |
| M335.016, theorem `LubinTate.standardLocalFieldValuationUnitsToFieldUnits_apply_coe` | 236–244 (docstring 236–237, `@[simp]` 238, statement 239–243, proof `rfl` 244) | `Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits_apply_coeStatement` |

The section parameters come from source lines 37–38, inside
`noncomputable section` and `namespace LubinTate`. The proposition is the
source theorem's type verbatim, with only namespace resolution.

## Reused interfaces

The single import is the paired data module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ValuationUnitsToFieldUnits`
(M335.015), which in turn supplies `standardLocalField` and the FM
`LocalField.valuationSubring` accessor. Mathlib supplies the unit and subtype
coercions.

## Modifications

The complete adaptation record is:

1. Extract only the statement of M335.016 and its docstring; omit its `rfl`
   proof and all other declarations of the module.
2. Replace the theorem by a `def` returning `Prop`, named with the
   `Statement` suffix. The theorem's explicit argument `u` becomes the
   definition's explicit parameter, after the unchanged section variables.
3. Omit the `@[simp]` attribute, which belongs to an eventual proof and is
   not meaningful for a Prop-valued definition.
4. Prefix the namespace `LubinTate` by `Langlands.NYLL`. The source `open`
   lines are not needed by the statement and are omitted.
5. Replace the six original module imports by the focused import above.
   Keep `noncomputable section`, closed by a final `end` as in the source;
   the source's `end LubinTate` becomes `end Langlands.NYLL.LubinTate`.
6. Add a prominent modification notice in the Lean header, a focused module
   overview and this document. Worker 413 made these adaptations on
   14 November 2026.

The proposition, its parameters and hypotheses are unchanged.

The original 2026 copyright, Apache-2.0 and authorship header is retained
verbatim. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
retained unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Verification

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), over
Library commit `7f5b5f04a855fc0b4671393213c87415a6ee2aaf` together with the
paired M335.015 module, this module compiles with zero errors and zero
warnings. Exact-target inspection of
`Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits_apply_coeStatement`
(private check `e38cbaa0-7245-4a95-96f6-5a4c54d03f8d`) reports a definition
with `statement_returns_prop: true`, no universe parameters, and axioms only
`propext`, `Classical.choice` and `Quot.sound`. The source pinned
Lean 4.35.0-rc2; no change was needed for Lean 4.34.0.

This module supplies no proof. A private probe (check
`470b0e3f-dc32-43ce-a880-a804b1d5f805`) confirmed only that the target
type-checks as `(standardLocalField K).valuationSubringˣ → Prop` and is closed
by `rfl`, as in the source; any proof is a separate later successor.
