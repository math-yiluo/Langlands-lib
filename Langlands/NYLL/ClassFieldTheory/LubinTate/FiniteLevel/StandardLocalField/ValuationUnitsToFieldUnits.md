# The canonical valuation-unit inclusion

This module extracts exactly source unit M335.015 as
`Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits`.
For a field `K : Type` with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
it is the monoid homomorphism

```lean
standardLocalFieldValuationUnitsToFieldUnits K :
  (standardLocalField K).valuationSubringˣ →* Kˣ
```

with value exactly

```lean
(integerUnitsToFieldUnits K).comp
  (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom
```

A unit of the valuation ring of the canonical local-field package
`standardLocalField K` is first carried back to a unit of the valuation-integer
subring `𝒪[K]` of the given valuative relation by the inverse of the canonical
unit equivalence `standardLocalFieldIntegerUnitsEquiv K`, and then included in
`Kˣ` by `integerUnitsToFieldUnits K`, which is `Units.map` of the algebra map
`𝒪[K] → K`. Both underlying rings are subrings of `K` with the same elements,
and both maps preserve the underlying element of `K`; consequently this
homomorphism sends a unit to the field unit with the same underlying element.
That coercion property is not asserted by this module; it is the separate
Prop-valued target
`Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits_apply_coeStatement`
(M335.016) in the paired module `ValuationUnitsToFieldUnitsCoeStatement`.

The parameters are exactly the source section variables: `K` explicit, at
universe level `Type` (not generalized), and the four instance arguments. No
other hypothesis, chosen valuation, bundle or global instance is introduced.
The declaration is `noncomputable`, as in the source.

## Source and correspondence

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean>),
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The full source file has SHA-256
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`, which
also matches the author's CI publication record in the supplement. The source
registrations are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

| Source unit and name | Source lines | Adapted declaration |
| --- | --- | --- |
| M335.015, `LubinTate.standardLocalFieldValuationUnitsToFieldUnits` | 229–234 (docstring 229–230, declaration 231–234) | `Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits` |

The section parameters come from source lines 37–38
(`variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`), inside `noncomputable section` (line 26) and
`namespace LubinTate` (line 30), with `open scoped ValuativeRel` (line 28) and
`open LocalFieldTheory.IsNonarchimedeanLocalField` (line 35), the last of which
resolves the source's unqualified `integerUnitsToFieldUnits`.
The result type, the defining expression and the docstring are unchanged
apart from namespace resolution.

## Reused interfaces

- `Langlands.NYLL.LubinTate.standardLocalFieldIntegerUnitsEquiv` (M335.011),
  from the published module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerUnitsEquiv`.
  Through its imports (`...StandardLocalField.IntegerEquiv` and
  `...StandardLocalField.Definitions`) it also supplies
  `Langlands.NYLL.LubinTate.standardLocalField` (M335.001) and FM's shared
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField` package
  with its `valuationSubring` accessor;
- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits`
  (M128.016), from the published module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`.

These two imports are the module's only imports. Mathlib supplies
`MulEquiv.symm`, `MulEquiv.toMonoidHom` and `MonoidHom.comp`. All reused
declarations are consumed by their published Lean names without alteration;
nothing is duplicated.

## Modifications

The complete adaptation record is:

1. Extract only M335.015 and its declaration docstring from the original
   module; omit all other declarations of the module (M335.001–.014 and
   M335.016–.021) and the original module overview.
2. Prefix the declaration namespace `LubinTate` by `Langlands.NYLL`, and
   replace the source's `open LocalFieldTheory.IsNonarchimedeanLocalField` by
   `open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. The
   other source `open` lines (`LocalFieldTheory`,
   `LocalFieldTheory.DiscreteValuationField`, its `CompleteDVF` namespace and
   `open scoped ValuativeRel`) are not needed by this declaration and are
   omitted.
3. Replace the six original module imports (DiscreteValuationField basics,
   principal units, Teichmüller decomposition, finite-extension complete DVF,
   ideal quotients and standard open subgroups) by the two focused published
   imports named above. No principal-unit, Teichmüller, ideal-transport or
   comparison-proof module is imported.
4. Keep the section variables, `noncomputable section` (closed by a final
   `end`, as in the source) and the explicit `noncomputable` modifier
   verbatim. The source's closing `end LubinTate` becomes
   `end Langlands.NYLL.LubinTate`.
5. Add a prominent modification notice in the Lean header, a focused module
   overview and this document. Worker 413 made these adaptations on
   14 November 2026.

There is no change to the mathematical value, type, parameters or hypotheses.

The original 2026 copyright, Apache-2.0 and authorship header is retained
verbatim. The supplement's ClassFieldTheory attribution list does not include
this source file. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Verification

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), over
Library commit `7f5b5f04a855fc0b4671393213c87415a6ee2aaf`, the module compiles
with zero errors and zero warnings (private check `b9a826ff-cbd8-451d-81e5-92fe601fe412`).
Inspection reports a definition with no universe parameters whose axioms are
only `propext`, `Classical.choice` and `Quot.sound`. The source pinned
Lean 4.35.0-rc2; no change was needed for Lean 4.34.0.

A separate private probe (check `470b0e3f-dc32-43ce-a880-a804b1d5f805`, not
part of this unit) confirmed by `rfl` that the definition is definitionally
the stated composite and that the M335.016 coercion assertion holds
definitionally, as the source's `rfl` proof expects.
