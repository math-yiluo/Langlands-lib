# NYLL intermediate-extension normality target

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module: `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransferFrobeniusGeometry.lean`.

| Unit | Source declaration | Adapted declaration | Source lines |
| --- | --- | --- | --- |
| `M068.003` | `ClassFormation.transferNormNaturality_intermediateExtension_normal` | `Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normalStatement` | `62–67` |

## Meaning

The proposition asserts that normality of the actual subgroup for `L/K`
restricts to `L/K'`. It retains explicit `K K' L`, the ordered proofs
`hLK'`, `hK'K`, and the named upper normality instance `hLnormal`.

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

The theorem becomes a Prop-valued definition with the `Statement` suffix;
its proof at lines 68–76 is omitted. The target assumes upper normality and
states lower normality; it does not install a lower-normality instance.

## Validation and scope

A successful `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module. A private comparison
module also checked equality of each entire unapplied constant to a separately
source-spelled reconstruction, retaining `extensionSubgroup` as a local
abbreviation; this checks the whole telescope and body together. This is a
development check, not independent semantic acceptance.

`transferNormNaturality_intermediateExtension_normalStatement` was individually inspected with `statement_returns_prop: true`.

These files do not provide a proof of any reciprocity theorem.
