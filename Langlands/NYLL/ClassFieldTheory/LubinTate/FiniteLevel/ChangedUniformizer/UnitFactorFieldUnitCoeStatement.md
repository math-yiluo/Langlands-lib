# Unit-factor coercion target

This module defines exactly the closed proposition
`Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit_coeStatement`.
For independent universes `u v`, it asserts

```lean
∀ {K : Type u} [Field K]
  (F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)
  (u : F.valuationSubringˣ),
  (Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit F u : K) =
    (u : F.valuationSubring)
```

The field and its field instance remain implicit; the chosen local-field
package and valuation-subring unit remain explicit. The right-hand side is
the unit's value in the actual valuation subring, then coerced into `K` as
required by the equality. There is no chosen uniformizer, finite level or
additional hypothesis. This module defines the proposition; its exact proof
is a separate publication.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean>),
commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The complete file was read, including
the namespace, universe and field-parameter context at lines 43–51 and the
M391.007 definition at lines 105–109. The source theorem M391.008 starts at
line 113; its statement and proof occupy lines 113–118. The file's SHA-256
is `684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
The source registrations are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Source unit and name | Adapted declaration |
| --- | --- |
| M391.008, `LubinTate.standardLubinTateUnitFactorFieldUnit_coe` | `Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit_coeStatement` |

The complete adaptations, made by Worker 328 on 14 November 2026, are:

1. Extract only M391.008's proposition, retaining the source's independent
   universes, binder order and explicitness, and exact equality. Enclose the
   full source telescope in `∀` inside a closed `def : Prop`.
2. Prefix the declaration namespace and reused NYLL names with
   `Langlands.NYLL`, and append `Statement` to the source theorem's name.
   Fully qualify `LocalField` instead of opening its source namespace.
3. Replace the twelve original imports by the sole published M391.007
   module, `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.UnitFactorFieldUnit`.
   It already supplies all interfaces needed to state the proposition.
4. Omit the source theorem's proof and `@[simp]` attribute. A proposition
   definition does not register a simplification theorem. Omit the surrounding
   `noncomputable section`, which is unnecessary for this Prop definition.
5. Adapt the declaration docstring to identify a statement, replace the
   broad source module overview with focused documentation, and add the
   modification notice and this correspondence document.

## Published interfaces and helper replacement

The sole import reuses the published
`Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit` (M391.007).
Its body applies
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`
(M388.001) to `F.toCompleteDVF` and the unit. The actual shared
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField` and its
`valuationSubring` abbreviation are imported transitively. No replacement
local-field interface, map or instance is introduced, and neither dependency
is edited.

The source proof invokes the wrapper
`LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply`
(M388.002). Mathlib already supplies the underlying formula as
`ValuationSubring.coe_unitGroupMulEquiv_symm_apply`, at
`Mathlib/RingTheory/Valuation/ValuationSubring.lean:514–515` in the approved
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
With the actual published M391.007 and M388.001 definitions, the following
focused compatibility example is checked privately:

```lean
example {K : Type u} [Field K]
    (F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)
    (u : F.valuationSubringˣ) :
    (Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit F u : K) =
      (u : F.valuationSubring) := by
  exact ValuationSubring.coe_unitGroupMulEquiv_symm_apply _ u
```

The first example follows Worker 309's private LN compatibility check and
was rechecked here against the current Library definitions.

The actual M388.001 map composes the inverse unit-group equivalence with
the subgroup inclusion. After unfolding these definitions, Mathlib's
formula gives precisely the displayed equality. A second private example
checks the same replacement directly for the actual M388.001 map and an
arbitrary published `CompleteDVF.{u, v} K`. Thus a duplicate M388.002 target
or proof is not a prerequisite for this target or its future proof. These
are development compatibility checks, not accepted proof publications.
The public Lean file contains only the Prop definition and imports M391.007
alone.

## Attribution and verification

The original 2026 copyright, Apache-2.0 license and authorship header is
retained verbatim: Naganori Yamaguchi (assisted by OpenAI Codex). Existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained unchanged;
their verified SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Focused compilation and exact declaration inspection use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and the Mathlib commit
above. Exact target check `2232ceaa-007e-4204-9bdc-9bec9642b556` passed
with zero errors or warnings, independent level parameters `u v` and
`statement_returns_prop: true`. Private compatibility check
`fc421639-3fd1-493d-a70f-9125c3b7e3e7` passed with zero errors or warnings,
using the same environment and actual published definitions. Development checks do not establish independent
acceptance or Library publication of a proof.
