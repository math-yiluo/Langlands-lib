# NYLL extension fixed representation action target

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module: `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`.

| Unit | Source declaration | Adapted declaration | Source lines |
| --- | --- | --- | --- |
| `M073.004` | `ClassFormation.extensionFixedRepresentation_action_coe` | `Langlands.NYLL.ClassFormation.extensionFixedRepresentation_action_coeStatement` | `87–95` |

## Meaning

The proposition states that the value of the actual quotient representation
action at `q` and invariant vector `a`, coerced to `A.V`, equals the relative
coset action at `q` on the vector identified with `A_L` by M073.001.

It retains implicit universe-zero `G`, group and topology instances, explicit
`A`, `K L`, `hLK`, explicit `hnormal`, then quotient element `q` and invariant
vector `a`, in their original order. No finiteness or continuity premise is
added. Both actions are actual published constructions, and the fixed-carrier
equivalence is supplied by the companion M073.001 definition pair.

## Modifications

Prefix the `ClassFormation` namespace with `Langlands.NYLL`. Replace broad
source imports with the focused imports in the Lean file. The abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact Mathlib
body `L.toSubgroup.subgroupOf K.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, as
permitted by the task. Every containment proof remains in the telescope even
where the expansion makes it unused. Extra grouping parentheses have no effect
on elaboration. No new global instance is introduced.

The source theorem becomes a Prop-valued `def` with the `Statement` suffix.
Its proof at lines 96–100 is omitted; no proof or simp attribute is published.
The source binder kinds and equality body are preserved. Focused imports
replace the broad NormLaws source import, since no norm construction is needed
for this proposition.

## Validation and scope

Development check `99d90ae7-cc11-413f-8e64-9e8cd3cf2741`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this module together with a
private comparison module. The latter reconstructs the source constants with
the original extension-subgroup abbreviation and checks equality of the entire
unapplied constants by `rfl`, preserving the full telescopes as well as bodies.
This is a development check, not independent semantic acceptance.

The check also inspected
`Langlands.NYLL.ClassFormation.extensionFixedRepresentation_action_coeStatement`
and reported `statement_returns_prop: true`, no universe parameters, and only
`propext`, `Classical.choice`, and `Quot.sound` as foundational assumptions.
The proposition is a target for a separate proof task; these files prove no
action comparison, norm identity or reciprocity result.
