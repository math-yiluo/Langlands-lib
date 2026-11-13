# NYLL naturality composite-quotient finiteness target

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
| `M066.013` | `ClassFormation.finiteReciprocityNaturality_tower_finite` | `Langlands.NYLL.PortInternal.M066.d013Statement` | `405–412` |

## Meaning

The proposition states that the quotient of `K` by `L'` is finite when
`K/K'` and `K'/L'` are finite. The three closed subgroups, the proofs
`hK'K`, `hL'K'`, and the two ordered `Finite` instances are unchanged.
These are coset quotients; no normality hypothesis is added.

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

The private source theorem becomes a public Prop-valued definition with the
required stable name `Langlands.NYLL.PortInternal.M066.d013Statement`.
Its proof at source line 413 is omitted; there is no dependency on that proof's
`relativeTowerQuotientFinite` theorem. This file supplies a statement target.

## Validation and scope

A successful `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module. A private comparison
module also checked equality of each entire unapplied constant to a separately
source-spelled reconstruction, retaining `extensionSubgroup` as a local
abbreviation; this checks the whole telescope and body together. This is a
development check, not independent semantic acceptance.

`Langlands.NYLL.PortInternal.M066.d013Statement` was individually inspected with `statement_returns_prop: true`.

These files do not provide a proof of any reciprocity theorem.
