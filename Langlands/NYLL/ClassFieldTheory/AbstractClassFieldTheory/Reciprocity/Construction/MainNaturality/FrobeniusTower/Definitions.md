# NYLL Frobenius tower restriction maps

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module: `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`.

| Unit | Source declaration | Adapted declaration | Source lines |
| --- | --- | --- | --- |
| `M066.003` | `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap` | `Langlands.NYLL.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap` | `82–102` |
| `M066.005` | `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMapContinuous` | `Langlands.NYLL.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMapContinuous` | `122–140` |

## Meaning

The first definition is the actual homomorphism from the quotient of `K'`
by its relative inertia for `L'` to the quotient of `K` by its relative inertia
for `L`. It uses `QuotientGroup.map` with `Subgroup.inclusion hK'K`.
The well-definedness proof sends the `L'` membership component through `hL'L`
and retains the ambient inertia membership component. The second bundles this
same map as a continuous monoid homomorphism. Its original continuity proof
reduces along the open quotient map and composes the quotient map with the
continuous subgroup inclusion.

Both keep `G : Type u`, its group and topology instances, then explicit `D`,
the `IsTopologicalGroup G` instance, explicit `K K' L L'`, the four ordered
containment proofs `hLK`, `hL'K'`, `hK'K`, `hL'L`, and the two named normality
instances in the original order. The published relative inertia construction
and normality instance M012.002/.003 are imported by Lean module name.

## Modifications

Prefix the `ClassFormation` namespace with `Langlands.NYLL`. Replace broad
source imports with the focused imports in the Lean file. The abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact Mathlib
body `L.toSubgroup.subgroupOf K.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, as
permitted by the task. Every containment proof remains in the telescope even
where the expansion makes it unused. Extra grouping parentheses have no effect
on elaboration. No new global instance is introduced.

The source universe `u`, binder kinds and actual quotient types are retained.
Both declarations remain data with their original construction bodies,
including all proof terms. Only M066.003/.005 are extracted; the intervening
represented-value theorem and later degree theorems are omitted. Unused
namespace openings are omitted.

## Validation and scope

Development check `99d90ae7-cc11-413f-8e64-9e8cd3cf2741`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this module together with a
private comparison module. The latter reconstructs the source constants with
the original extension-subgroup abbreviation and checks equality of the entire
unapplied constants by `rfl`, preserving the full telescopes as well as bodies.
This is a development check, not independent semantic acceptance.

These maps do not prove any Frobenius naturality or reciprocity theorem.
