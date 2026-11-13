# Field principal-unit antitonicity: statement target

This module defines the proposition
`Langlands.NYLL.LocalClassFieldTheory.fieldPrincipalUnits_antitoneStatement`.
Its complete body is

```lean
∀ (K : Type) [Field K] [ValuativeRel K] {m n : ℕ},
  m ≤ n →
    Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K n ≤
      Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K m
```

Thus, for a field with a supplied valuative relation, increasing the natural
index gives a smaller subgroup of the field's units. Both indices include
zero. Here `≤` between subgroups is subgroup inclusion. The field is in
`Type 0`, exactly as in the original theorem.

The filtration is the published
`Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits`, imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Definitions`.
Its index-`n` subgroup is the image in `Kˣ` of the units of the actual
valuation ring congruent to one modulo the `n`-th power of its maximal ideal.
The published definition uses the canonical units inclusion; its
[documentation](../../../../ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups/Definitions.md)
records the definitional comparison with the original inclusion wrapper.

The only hypotheses are `Field K`, `ValuativeRel K`, and `m ≤ n`.
The proposition adds no topology, local-field, discreteness, completeness,
residue-field, extension or Artin-map hypothesis.

## Original source and exact correspondence

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Conductor.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Conductor.lean#L34-L39),
lines 34–39 (source unit M290.001). The retained docstring is at line 33;
the enclosing namespace and openings are at lines 28–31.
The complete original file has SHA-256
`8000c3bea736ec102e4c879ad0da46d84eaae22d8091861493085966ce05c82c`.

The source passage was read directly from the registered snapshot at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its source registrations are
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No errata entry for either registration was present in the supplied Library.

| Original source | Adapted target |
| --- | --- |
| `LocalClassFieldTheory.fieldPrincipalUnits_antitone` | `Langlands.NYLL.LocalClassFieldTheory.fieldPrincipalUnits_antitoneStatement` |
| `(K : Type) [Field K] [ValuativeRel K]` | The same binders, universally quantified inside the proposition |
| `{m n : ℕ} (hmn : m ≤ n)` | `∀ {m n : ℕ}, m ≤ n → ...` inside the proposition |
| `LocalFieldTheory.fieldPrincipalUnits K n ≤ LocalFieldTheory.fieldPrincipalUnits K m` | The same inclusion, using the published `Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits` |

The entire theorem type, including its field and instance binders, becomes
the body of a closed `def ... : Prop`. The definition has no universe
parameters. The anonymous implication premise corresponds exactly to the
source argument `hmn`; its proof is not used to define the proposition.

## Modification and attribution record

Worker 315 made the following changes for this focused statement unit:

- Prefix the original namespace with `Langlands.NYLL` and append `Statement`
  to the original declaration name.
- Replace the proved theorem by a `Prop` definition whose body is its full
  type. The original proof
  `Subgroup.map_mono (principalUnits_antitone K hmn)` is omitted.
- Replace the three original imports (`TopologicalReciprocity`,
  `StandardOpenSubgroups`, and `Mathlib.FieldTheory.Galois.Abelian`) by the
  published focused `StandardOpenSubgroups.Definitions` import.
- Fully qualify the filtration name and omit the unused `open LocalFieldTheory`,
  `open scoped ValuativeRel`, and `noncomputable section`.
- Replace the original conductor-wide module documentation by documentation
  of this target and add source/adaptation comments. Retain the theorem's
  original docstring and copyright/author header.

The published filtration definition is reused without alteration. The
original source module has no applicable patch10 edit in the public port
partition. This unit introduces no proof of the target or further conductor
declaration; M290.002–M290.010 remain outside its scope.

The upstream Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained in the Library.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected original Conductor path has no entry in that NOTICE. The
contribution copies no additional third-party implementation.

## Validation

Development check `a1efa67a-4657-4b86-8b7d-170f90675a7b` compiled this focused
module and inspected the exact proposition declaration through the approved
Lean service in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). It returned
`ok: true`, exit code zero, zero errors and zero warnings. Inspection reports
`kind: definition`, no universe parameters, and `statement_returns_prop: true`;
the listed assumptions are `propext`, `Classical.choice`, and `Quot.sound`.
This successful focused build supports the reduced import list.

The source used Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Independent semantic acceptance and integration are separate from the
development check.
