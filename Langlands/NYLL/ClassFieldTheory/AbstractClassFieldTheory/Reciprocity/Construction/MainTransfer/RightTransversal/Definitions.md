# NYLL chosen right transversal for transfer

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
| `M071.017` | private `ClassFormation.chosenTransferNormNaturalityRightTransversal` | `Langlands.NYLL.PortInternal.M071.d017` | `576–583` |

This same-module data prerequisite is included because the required M071.022
`transferNormNaturalityNormWitness` uses it.

## Meaning

The definition chooses a right transversal for the subgroup
`transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K` of `K/L`.
The actual representative set is `Set.range Quotient.out`. Its complement
certificate is the original `Subgroup.isComplement_range_right Quotient.out_eq'`.
It is a chosen set with its certificate, with no finiteness hypothesis.

The complete telescope retains implicit `G : Type u`, its group and topology
instances, explicit `K K' L`, then `hLK'`, `hK'K`, and the two named normality
instances `hLnormal`, `hL'normal`, in that order.

## Modifications

The private source name becomes the specified public internal name
`Langlands.NYLL.PortInternal.M071.d017`; its data type and construction body
are unchanged. The source's `noncomputable` declaration inside a noncomputable
section is expressed as `def` inside a noncomputable section. The source
universe `u` and binder kinds are preserved.

The abbreviation `CyclicCohomology.extensionSubgroup K L hLK` is expanded to
its exact Mathlib defining term `L.toSubgroup.subgroupOf K.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, as
permitted by the task. Every containment proof is retained even where the
expansion makes it unused. No global instance is added.

The focused imports supply the namespaced M071.001/.004 intermediate
construction and Mathlib's `RightTransversal` and complement certificate.
Broad source imports, unrelated openings, declarations and theorem proofs are
omitted. The docstring spells the quotient as `K/L` rather than `G(L/K)`.

## Validation and scope

Development check `467b0ae3-1024-4974-9c20-3c32b69c1b2f` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this definition and a private
comparison module. That module reconstructs the source definition with its
original subgroup abbreviation and checks equality of the entire unapplied
constant by `rfl`, testing telescope and body together. Inspection reports a
definition at universe `u` with only the allowed foundational assumptions
`propext`, `Classical.choice`, and `Quot.sound`.

This is construction data; development validation does not constitute
independent semantic acceptance or a proof of transfer–norm naturality.
