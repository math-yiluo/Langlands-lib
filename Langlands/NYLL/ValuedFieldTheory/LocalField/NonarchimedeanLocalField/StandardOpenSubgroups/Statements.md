# Principal units inside neighborhoods and open subgroups

This module gives the two Prop-valued targets M289.003 and M289.004 under
`Langlands.NYLL.LocalFieldTheory`. Both retain the complete source telescope

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
```

with a single arbitrary universe `u`. Here `IsNonarchimedeanLocalField` is
Mathlib's class for a locally compact, nontrivially valued field with the
topology induced by its supplied `ValuativeRel`. The topology on `Kˣ` is
Mathlib's canonical unit-group topology from the supplied topology on `K`.

| Target (in `Langlands.NYLL.LocalFieldTheory`) | Further explicit source parameters | Proposition |
| --- | --- | --- |
| `exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement` | `(U : Set Kˣ) (hU : U ∈ Filter.nhds (1 : Kˣ))` | `∃ n : Nat, 1 ≤ n ∧ (fieldPrincipalUnits K n : Set Kˣ) ⊆ U` |
| `exists_fieldPrincipalUnits_le_of_isOpenStatement` | `(H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ))` | `∃ n : Nat, 1 ≤ n ∧ fieldPrincipalUnits K n ≤ H` |

The first says that every neighborhood of one in the actual field-unit group
contains a positive principal-unit subgroup. The second says that every open
subgroup contains such a subgroup. The subgroup order `≤` means containment
of all its elements; the first proposition uses containment of the underlying
sets. Both require `1 ≤ n`, rather than allowing a zero witness.

The hypotheses `hU` and `hH` remain explicit parameters even though a target's
conclusion does not depend on their proof terms. Each fully applied definition
returns `Prop`. This module states the targets; it supplies neither proof.

The published `fieldPrincipalUnits` is imported from the sibling
[Definitions module](Definitions.md). It is the image of
`principalUnits K n : Subgroup 𝒪[K]ˣ` under
`Units.map (algebraMap 𝒪[K] K).toMonoidHom`. The integer-unit subgroup consists
of units congruent to one modulo `𝓂[K]^n`. Thus the targets use the actual
valuation ring, its maximal ideal and the canonical inclusion into the field.

## Source correspondence and modifications

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, at the exact path
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean`.
Its full-file SHA-256 is
`9cf6baf50519f650504762782a5aed12500479b911fc1ac4db9a138207097d7d`.

| Source unit and original declaration (in `LocalFieldTheory`) | Exact original lines | Adapted target |
| --- | --- | --- |
| M289.003, `exists_fieldPrincipalUnits_subset_of_mem_nhds` | docstring 43; signature 44–48; proof 48–84 | `exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement` |
| M289.004, `exists_fieldPrincipalUnits_le_of_isOpen` | docstring 86–87; signature 88–92; proof 93 | `exists_fieldPrincipalUnits_le_of_isOpenStatement` |

In the raw pinned file, line 45 (the task's locator for M289.003) begins its
`K` binder; the theorem keyword is on line 44. The declaration name and
signature above identify the same source unit.

The source passages were read directly from the retained registered snapshot at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The original registration is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching errata file for either source ID was present in the supplied
Library's `notes/errata/`.

Worker 323 made the following adaptations on 13 November 2026:

- Prefix the source namespace with `Langlands.NYLL`.
- Replace the two theorem declarations by `def`s returning `Prop`, append
  `Statement` to each name, and omit both source proof bodies.
- Retain every source parameter, instance, explicit hypothesis, argument order
  and conclusion, including the arbitrary universe and `1 ≤ n`; spell `ℕ`
  as `Nat`.
- Replace the broad original `PrincipalUnitQuotients` import by the published
  `StandardOpenSubgroups.Definitions` and `Mathlib.NumberTheory.LocalField.Basic`.
  The latter supplies the original Mathlib local-field class and topology.
- Retain the source noncomputable section and `ValuativeRel` scoped opening;
  omit the source's unused namespace openings and explicitly open `Filter`
  for `nhds`. Replace the broad module documentation by documentation for
  these two targets, and add this modification notice.

The source docstrings are retained. No source proof or other worker's modified
implementation is reused. The already published definition is reused by Lean
name; this module does not redefine the field-unit inclusion or principal
units and adds no instances.

The proof of M289.003 in the original uses M132.012,
`exists_maximalIdeal_pow_subset_nhds_zero`. Its published target is in
`PrincipalUnitQuotients.TopologyStatements`; that proof is a separate obligation
and is unnecessary for defining these propositions. Neither that target nor a
proof module is imported here. The source uniformizer subgroup M289.002 and
the finite-index theorem M289.005 are outside this pair.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The unchanged Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained in the Library.
Their checked SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The modification notice identifies this extraction and adaptation.

## Focused development checks

The successful checks used environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) and entry module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Statements`.

| Inspected target | Development diagnostic ID |
| --- | --- |
| `exists_fieldPrincipalUnits_subset_of_mem_nhdsStatement` | `44edb5b0-8468-4f91-9658-0d2b2e1a91d6` |
| `exists_fieldPrincipalUnits_le_of_isOpenStatement` | `4babb24d-b476-4f93-9670-fad4a22598de` |

Both returned `ok: true`, exit code zero, `kind: definition`,
`level_parameters: ["u"]` and `statement_returns_prop: true`.
The checks reported zero errors and two unused-variable warnings for the
intentionally retained hypothesis parameters `hU` and `hH`. Inspection listed
only the standard assumptions `propext`, `Classical.choice` and `Quot.sound`.
Development compilation and target inspection are separate from independent
semantic review and publication.
