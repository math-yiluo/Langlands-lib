# Principal units inside every open subgroup

The theorem
`Langlands.NYLL.LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen`
proves the existing Library target
`Langlands.NYLL.LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpenStatement`.
It retains the complete telescope

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
(H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ))
```

for arbitrary universe `u`. The conclusion is
`∃ n : Nat, 1 ≤ n ∧ fieldPrincipalUnits K n ≤ H`.
Here the principal-unit subgroup and its map from valuation-ring units into
field units are the published definitions; this module adds no definitions
or instances.

## Implemented proof

A subgroup contains its identity, by `H.one_mem`. Since its underlying set is
open, Mathlib's `IsOpen.mem_nhds` gives
`(H : Set Kˣ) ∈ Filter.nhds (1 : Kˣ)`.
The imported theorem
`exists_fieldPrincipalUnits_subset_of_mem_nhds` then supplies a natural number
`n`, the positive bound `1 ≤ n`, and containment of the underlying set of
`fieldPrincipalUnits K n` in `H`.
Containment of underlying sets is definitionally the subgroup inequality
`fieldPrincipalUnits K n ≤ H`, so the entire source application proves the
fully applied target directly. No additional proof hypothesis is introduced.

The neighborhood theorem is imported by Lean name from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.U003.Proofs`.
The unchanged target is imported from the sibling
[Statements module](../Statements.md).

## Source correspondence and modifications

The proof adapts source unit M289.004 in Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean`.
The original docstring is at lines 86–87, theorem signature at lines 88–92,
and proof term at line 93. The source file has SHA-256
`9cf6baf50519f650504762782a5aed12500479b911fc1ac4db9a138207097d7d`.
It was read from the retained registered snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

The source registrations are
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching errata page for these source IDs was present in the supplied Library.

Worker 560 made these adaptations on 14 November 2026:

- Isolate M289.004 in its own proof module and prefix the source namespace with
  `Langlands.NYLL`.
- Replace the broad `PrincipalUnitQuotients` import with the focused published
  target module and neighborhood proof module.
- Retain every source parameter, instance, hypothesis and its order, including
  the arbitrary universe, and state the result as the fully applied published
  target instead of repeating its defining proposition.
- Retain the source proof application unchanged, relying on definitional
  reduction of the two statement definitions.
- Retain the source noncomputable section and `ValuativeRel` scoped opening,
  omit redundant namespace openings, and use focused documentation.

The proof only establishes M289.004; the finite-index and uniformizer result
M289.005 is outside its scope.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The existing Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean modification notice identifies this focused adaptation.

## Development validation

A Lake build and theorem inspection in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` succeeded with zero errors and
zero warnings, diagnostic `6829497d-7e56-4048-85cc-848423fe9eeb`.
Inspection reports the universe parameter `[u]` and only the standard
assumptions `propext`, `Classical.choice` and `Quot.sound`.
This development check is separate from exact-target validation, independent
semantic review and publication.
