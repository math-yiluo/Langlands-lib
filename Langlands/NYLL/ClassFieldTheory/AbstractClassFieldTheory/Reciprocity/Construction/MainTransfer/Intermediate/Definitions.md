# NYLL intermediate quotient inclusion and image

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
| `M071.001` | `ClassFormation.transferNormNaturalityIntermediateInclusion` | `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion` | `36–45` |
| `M071.004` | `ClassFormation.transferNormNaturalityIntermediateSubgroup` | `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateSubgroup` | `92–100` |

## Meaning

The first definition is the actual quotient-group homomorphism from
`K'/L` to `K/L`, constructed by the published naturality restriction with the
source arguments unchanged. The second is its monoid-homomorphism range,
a subgroup of `K/L`. Both retain the ordered `K K' L`, `hLK'`, `hK'K`,
and named normality instances `hLnormal`, `hL'normal`.

## Modifications

The `ClassFormation` namespace is prefixed by `Langlands.NYLL`. Broad source
imports and unused namespace openings are replaced by the focused imports in the
Lean file. The source abbreviation `CyclicCohomology.extensionSubgroup K L hLK`
is expanded to its exact Mathlib defining term
`L.toSubgroup.subgroupOf K.toSubgroup` (source
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54).
Every containment proof remains a parameter even where this expansion makes it
unused. The source universe `u`, implicit `G`, group and topology instances,
binder kinds, and ordered explicit and instance arguments are preserved. No new
global instance is introduced.

Both declarations remain data with their original names and complete
construction bodies. The imported naturality restriction is the namespaced
adaptation of M066.001. Unrelated source definitions and theorem proofs are
omitted. The companion `Statements` module contains the M071.002/.003 targets.

## Validation and scope

A successful `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module. A private comparison
module also checked equality of each entire unapplied constant to a separately
source-spelled reconstruction, retaining `extensionSubgroup` as a local
abbreviation; this checks the whole telescope and body together. This is a
development check, not independent semantic acceptance.

Both constructions occur in the successful whole-constant equality check.

These files do not provide a proof of any reciprocity theorem.
