# NYLL intermediate quotient inclusion targets

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
| `M071.002` | `ClassFormation.transferNormNaturalityIntermediateInclusion_mk` | `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion_mkStatement` | `52–61` |
| `M071.003` | `ClassFormation.transferNormNaturalityIntermediateInclusion_injective` | `Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion_injectiveStatement` | `66–73` |

## Meaning

The first proposition gives the inclusion's value on a quotient
representative `k'`: the class of its subgroup inclusion in `K`. The second
asserts injectivity of that actual homomorphism. Both retain the ordered closed
subgroups, containment proofs and two named normality instances; the first also
retains the final explicit `k'` argument. The companion `Definitions` module
contains the actual inclusion and range constructions M071.001/.004.

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

Each source theorem becomes a Prop-valued definition with the `Statement`
suffix. The original proofs at line 62 and lines 74–89 are omitted; the source
`@[simp]` attribute on the represented-value theorem is omitted. No injectivity
proof is assumed in either target's telescope.

## Validation and scope

A successful `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module. A private comparison
module also checked equality of each entire unapplied constant to a separately
source-spelled reconstruction, retaining `extensionSubgroup` as a local
abbreviation; this checks the whole telescope and body together. This is a
development check, not independent semantic acceptance.

Both `transferNormNaturalityIntermediateInclusion_mkStatement` and `transferNormNaturalityIntermediateInclusion_injectiveStatement` were individually inspected with `statement_returns_prop: true`.

These files do not provide a proof of any reciprocity theorem.
