# NYLL extension fixed representation carrier equivalence

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
| `M073.001` | `ClassFormation.extensionFixedRepresentationEquiv` | `Langlands.NYLL.ClassFormation.extensionFixedRepresentationEquiv` | `35–57` |

## Meaning

This is the actual additive equivalence from the invariant carrier of
`extensionFixedRepresentation A K L hLK hnormal` to the ambient fixed subgroup
`A_L`. Both maps preserve the underlying coefficient vector and transport its
fixedness certificate. The original subtype proofs establish both inverse
identities and additivity.

The telescope retains implicit `G : IntegralRepGroupType`, group and topology
instances, explicit `A : Rep ℤ G`, `K L`, `hLK`, and explicit `hnormal` in that
order. The acting group and coefficient carrier are universe zero, as forced
by the source's extension representation. The published quotient representation
and ambient fixed subgroup are imported, not replaced by supplied objects.

## Modifications

Prefix the `ClassFormation` namespace with `Langlands.NYLL`. Replace broad
source imports with the focused imports in the Lean file. The abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact Mathlib
body `L.toSubgroup.subgroupOf K.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, as
permitted by the task. Every containment proof remains in the telescope even
where the expansion makes it unused. Extra grouping parentheses have no effect
on elaboration. No new global instance is introduced.

The source's noncomputable section and complete `where` construction are
preserved. Unused scope openings and all source theorem proofs are omitted.
The companion Action/Statements module contains the M073.004 proposition.
The M071.014 source adapter has the same telescope and underlying maps. Integration uses this M073.001 declaration for both source units; the MainTransfer/FixedCarrier module imports it, and the M071.022 norm witness uses it directly. Its meaning and the M073.001 construction are unchanged.

## Validation and scope

Development check `99d90ae7-cc11-413f-8e64-9e8cd3cf2741`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this module together with a
private comparison module. The latter reconstructs the source constants with
the original extension-subgroup abbreviation and checks equality of the entire
unapplied constants by `rfl`, preserving the full telescopes as well as bodies.
This is a development check, not independent semantic acceptance.

This construction does not prove the action comparison or any norm theorem.
