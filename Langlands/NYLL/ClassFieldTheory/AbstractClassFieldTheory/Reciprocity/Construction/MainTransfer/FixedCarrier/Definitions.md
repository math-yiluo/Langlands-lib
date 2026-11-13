# NYLL transfer fixed representation carrier equivalence

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module: `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`.

| Unit | Source declaration | Adapted declaration | Source lines |
| --- | --- | --- | --- |
| `M071.014` | `ClassFormation.transferNormNaturalityExtensionFixedEquiv` | `Langlands.NYLL.ClassFormation.extensionFixedRepresentationEquiv` | `522–538` |

## Meaning

This actual additive equivalence identifies the invariant carrier in the
quotient representation for `L | K` with the ambient fixed subgroup `A_L`.
Its forward and inverse maps preserve the underlying vector. The forward map
forms the original `extensionSubgroup` element using `Subgroup.inclusion hLK`;
the inverse converts an extension-subgroup element into an element of `L`.
The canonical equivalence has these same underlying maps; its proof fields agree by proof irrelevance.

The ordered telescope keeps implicit `G : IntegralRepGroupType`, group and
topology instances, explicit `A : Rep ℤ G`, `K L`, `hLK`, and explicit
normality proof `hnormal`. The acting group and coefficient carrier remain
universe zero as in the source. Published quotient-representation and ambient
fixed-subgroup data supply the actual objects.

## Modifications

Prefix the `ClassFormation` namespace with `Langlands.NYLL`. Replace broad
source imports with the focused imports in the Lean file. The abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact Mathlib
body `L.toSubgroup.subgroupOf K.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, as
permitted by the task. Every containment proof remains in the telescope even
where the expansion makes it unused. Extra grouping parentheses have no effect
on elaboration. No new global instance is introduced.

The independently accepted M073.001 construction has the same telescope and underlying maps. Integration retains it as `Langlands.NYLL.ClassFormation.extensionFixedRepresentationEquiv` and removes the duplicate M071.014 declaration. This module imports the canonical FieldRepresentation/FixedCarrier/Definitions module, and M071.022 uses its equivalence directly. The source-level M071.014 name in the table records provenance rather than a second exported constant.

## Validation and scope

Before consolidation, development check `99d90ae7-cc11-413f-8e64-9e8cd3cf2741`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this module together with a
private comparison module. The latter reconstructs the source constants with
the original extension-subgroup abbreviation and checks equality of the entire
unapplied constants by `rfl`, preserving the full telescopes as well as bodies.
This is a development check, not independent semantic acceptance.

This is construction data, without a proof of transfer–norm naturality.
