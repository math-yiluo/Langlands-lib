# Local compactness of the universe-zero representative: statement

`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_locallyCompactStatement.{u}`
is the following universal Prop-valued definition:

```lean
def shrinkLocalField_locallyCompactStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    LocallyCompactSpace (Shrink.{0} K)
```

The universe `u` is arbitrary. For each carrier `K`, the four supplied
instances occur in exactly this order: `Field K`, `ValuativeRel K`,
`TopologicalSpace K`, and `IsNonarchimedeanLocalField K`. The last instance
certifies the local-field properties for the preceding supplied structures.
There is no additional smallness premise.

The local `Small.{0} K` instance is the published theorem
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small K`,
imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SmallProof`.
The conclusion refers to Mathlib's actual `Shrink.{0} K : Type 0`.
`Mathlib.Topology.Instances.Shrink` supplies its topology by transporting
the supplied `TopologicalSpace K` along `equivShrink K`; explicitly, its
instance is `(equivShrink K).symm.topologicalSpace`.
The corresponding Mathlib homeomorphism has type
`Shrink.homeomorph K : K ≃ₜ Shrink.{0} K`.
The target takes no chosen equivalence and imposes no canonical-topology
restriction. This file introduces no global instance.

This unit defines the proposition only. Its exact proof is reserved for a
later proof child with the intended name
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_locallyCompact`.
It contains no later M422.005–009 property, Artin-family transport or host
assembly.

## Source correspondence and adaptations

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[ShrinkTransport.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The full source file was read and its SHA-256 checked as
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
Its complete field parameters are at lines 27–28, its private smallness
wrapper at lines 30–31, and its local-compactness theorem at lines 49–54
(inventory row M422.004).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.shrinkLocalField_locallyCompact` | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_locallyCompactStatement` |

The original theorem signature is packaged as a universal `Prop` definition,
retaining its arbitrary universe and all supplied instances. The source's
private `smallLocalField K` wrapper is replaced by direct local use of the
published `nonarchimedeanLocalField_small K`. The namespace gains
`Langlands.NYLL`, and the statement name gains `Statement`. The original
smallness import is replaced by the published smallness proof module, and
Mathlib's Shrink topology import is retained. The original field-Shrink
import, valuation definitions and theorem proof are not needed to state
this proposition. No feasibility draft or compatibility patch is reused.

The registered original collection is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
its supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project or pinned-source `notes/errata` directory was present
at preparation.

The Lean header preserves the original 2026 copyright, Apache-2.0
attribution and authorship, including OpenAI Codex assistance, and records
Worker 1782's adaptations. The existing
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) were checked byte for byte
against the pinned originals. Their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
