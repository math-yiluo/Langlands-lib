# Local compactness of the universe-zero representative: proof

`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_locallyCompact.{u}` proves
exactly the published proposition
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_locallyCompactStatement.{u}`,
imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkLocallyCompactStatement`.
The theorem has no additional parameters or premises. The unchanged target
universally quantifies `K : Type u` and the supplied instances `Field K`,
`ValuativeRel K`, `TopologicalSpace K`, and `IsNonarchimedeanLocalField K`,
in that order. Its universe `u` is arbitrary.

## Implemented proof

After introducing the carrier and all four instances, the proof installs
`Small.{0} K` locally using the published
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small K`.
This is the same local smallness choice used in the target. The conclusion is
`LocallyCompactSpace (Shrink.{0} K)`, where the carrier lies in `Type 0`.

Mathlib's `IsNonarchimedeanLocalField K` extends `LocallyCompactSpace K` for
the supplied `TopologicalSpace K`. The topology on `Shrink.{0} K` is Mathlib's
transport of that supplied topology:
`(equivShrink K).symm.topologicalSpace`. In particular,
`Shrink.homeomorph K : K ≃ₜ Shrink.{0} K`. Its inverse has direction
`Shrink.{0} K ≃ₜ K`, so
`(Shrink.homeomorph K).symm.isOpenEmbedding` embeds the small carrier into
the locally compact space `K`. Applying
`Topology.IsOpenEmbedding.locallyCompactSpace` gives local compactness of
its domain, as required. The implementation is the original one-line
transport argument after introducing the universal target's parameters.

No extra smallness, chosen equivalence, or local-compactness hypothesis is
introduced, and the proof installs no global instance. It proves M422.004
only. The subsequent M422.005–009 properties, Artin-family transport and
host assembly remain separate obligations.

## Source correspondence and adaptations

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[ShrinkTransport.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The full source file was read and its SHA-256 verified as
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
The field parameters are at lines 27–28, the private smallness wrapper at
lines 30–31, and the local-compactness theorem at lines 49–54
(inventory row M422.004).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.shrinkLocalField_locallyCompact` | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_locallyCompact` |

The namespace gains `Langlands.NYLL`. The theorem now proves the complete
universal Library proposition, with explicit introductions of its carrier
and four supplied instances. The source's private `smallLocalField K`
wrapper is replaced by local use of the published
`nonarchimedeanLocalField_small K`. The local typed `let` and homeomorphism
proof are retained. The imports are reduced to
the published target, which already imports the smallness proof and
Mathlib's Shrink topology. The original field-Shrink import and preceding
valuation constructions are unnecessary for this topological result.
The target and all its imported Lean/Markdown pairs are preserved.

The registered original collection is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
its supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project, published-tree or pinned-source `notes/errata`
directory was present at preparation.

The Lean header preserves the original 2026 copyright, Apache-2.0
attribution and authorship, including OpenAI Codex assistance. Worker 1782
adapted this focused proof and wrote its documentation. No feasibility
draft or compatibility patch is reused. The existing
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) were checked byte for byte
against the pinned originals; their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
