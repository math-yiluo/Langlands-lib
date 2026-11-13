# A valuation-ring unit as a field unit

This module extracts exactly source unit M391.007 as
`Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit`.
For independent universes `u v`, a field `{K : Type u} [Field K]`,
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K`,
and `u : F.valuationSubringˣ`, it returns a unit of `K`. Its value is exactly

```lean
Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits
  F.toCompleteDVF u
```

Thus this definition applies the shared valuation-subring unit inclusion to
the unit and the complete discrete valuation field underlying `F`.
Its parameters are only `K`, its field instance, `F`, and the valuation-ring
unit. This module contains no coercion theorem, finite-level construction, or
norm-membership statement.

## Source and correspondence

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean>),
lines 106–109, at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The full source file has SHA-256
`684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
The source registrations are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

| Source unit and name | Adapted declaration |
| --- | --- |
| M391.007, `LubinTate.standardLubinTateUnitFactorFieldUnit`, lines 106–109 | `Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit` |

The source's independent universes, implicit field parameter and instance,
explicit local-field and unit parameters, result type `Kˣ`, and
`noncomputable def` status are retained. The defining expression is unchanged
apart from namespace qualification.

## Reused interfaces and modifications

The module reuses
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`,
its `toCompleteDVF` projection and `valuationSubring` accessor from FM
M334.001–005, and
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`
from LN M388.001.
Both are imported from their published Library modules:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap.Definitions`.

The local-field valuation-subring abbreviation unfolds to the valuation subring
of `F.toCompleteDVF`, so the supplied unit has exactly the domain type expected
by the homomorphism. Its existing monoid-homomorphism application supplies the
resulting field unit. No additional instance is declared.

The complete adaptation record is:

1. Extract only M391.007 and its declaration docstring from the original module;
   omit the other changed-uniformizer declarations and the original module
   overview about them.
2. Prefix the declaration namespace and both referenced NYLL namespaces by
   `Langlands.NYLL`. Fully qualify the local-field type and the unit inclusion,
   replacing the source's `open LocalFieldTheory.DiscreteValuationField`.
3. Replace the twelve original module imports by focused imports supplying the
   shared local-field package and unit inclusion, at the two paths above.
4. Keep `universe u v` and `{K : Type u} [Field K]`. Omit the surrounding
   `noncomputable section`, since the declaration retains its explicit
   `noncomputable` modifier. Put the result type on the unit-parameter line
   without changing the telescope.
5. Add a focused module overview, a prominent modification notice in the Lean
   header, and this source-correspondence document. Worker 319 made these
   adaptations on 13 November 2026.

There is no change to the mathematical value, no replacement bundle or
valuation, and no additional hypothesis or global instance.

The original 2026 copyright, Apache-2.0 and authorship header is retained
verbatim. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
retained unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

## Verification

The two shared interfaces are independently accepted and published in the
Library. Focused compilation and declaration inspection passed with no errors
or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
with independent level parameters `u` and `v`.
