# The topology of the induced valuative relation

`Langlands.NYLL.LocalFieldTheory.ValuedTopologyStatement.{u,v}` is a proposition
definition. It states that for every `F : Type u` and `Γ : Type v`, with
`Field F`, `LinearOrderedCommGroupWithZero Γ`, `MulArchimedean Γ`, `Valued F Γ`,
and `Valuation.IsNontrivial (Valued.v : Valuation F Γ)`, the following holds:
after locally installing
`ValuativeRel.ofValuation (Valued.v : Valuation F Γ)`, the supplied topology on
`F` satisfies `IsValuativeTopology F`.

The universes `u` and `v` are independent. All five source hypotheses remain
quantified, including multiplicative Archimedeanness and nontriviality. The
topology is the one inherited from the given `Valued F Γ` instance; the local
`letI` introduces only the valuative relation. This file defines the target
proposition and contains no proof of it or new global instance.

## Source and exact adaptation

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuedTopology.lean`.
The theorem `LocalFieldTheory.isValuativeTopology_of_valued_ofValuation` has its
signature at lines 27–33 and proof at lines 34–66. The entire 68-line file was
read. Its SHA-256 is
`4b160f30167a0f9eb46b5b6d696a8de1ae46b5c10458202a7d4c0b6b481d5cbf`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the file is under
`n-yamaguchi-0729--ClassFieldTheory/source/` in that source collection.
The local original is
[ValuedTopology.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuedTopology.lean>).

The exact original-to-adapted map is:

| Original | Adaptation |
| --- | --- |
| `LocalFieldTheory.isValuativeTopology_of_valued_ofValuation` | `Langlands.NYLL.LocalFieldTheory.ValuedTopologyStatement` |
| Theorem signature, lines 27–33 | Universally quantified body of a `def : Prop`, with identical argument order, hypotheses, local relation and conclusion |
| `Mathlib.Topology.Algebra.Valued.ValuativeRel` import | Unchanged; the only import |
| Theorem proof, lines 34–66 | Omitted from this statement contribution |
| `noncomputable section` and unused scoped opening | Omitted because this proposition definition does not need them |

This file was adapted directly from the pinned original; no proof or source
change from the feasibility draft's patch10 was reused. No applicable errata
file was present for either registered NYLL source at preparation.

## Dependencies and future proof context

The approved environment uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. All mathematical definitions in the
target are imported from Mathlib. No NYLL support definition is required.

The imported Mathlib file provides `IsValuativeTopology.of_zero` and a
construction of a `Valued` instance from a valuative topology. The latter has
the reverse direction and is not this statement. The Library's
`Langlands.PadicField.canonicalTopologicalData` constructs a particular
topology-compatible relation for finite p-adic extensions; it does not state
this arbitrary-field, arbitrary-value-group target.

For a future separate proof, the source introduces compatibility and
nontriviality for the induced relation, applies
`IsValuativeTopology.of_zero`, and compares zero neighborhoods using
`Valued.mem_nhds_zero` and
`ValuativeRel.ValueGroupWithZero.orderMonoidIso`. The two directions transport
unit radii across that order isomorphism and compare the corresponding strict
valuation bounds. This describes the source's proof route only; it is not an
implemented proof or a proof acceptance claim for this contribution.

## Attribution

The original copyright and author header is preserved in the Lean file.
Worker 315's modifications are recorded there and above. The original
Apache-2.0 [LICENSE](../../../../../licenses/NYLL/LICENSE) and full
[NOTICE](../../../../../licenses/NYLL/NOTICE) are retained byte for byte under `licenses/NYLL/`.
Their SHA-256 hashes are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This selected source file is absent from the root NOTICE inventory and all
five `ANTHROPIC_FLT_SOURCE.md` inventories in the registered supplement
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The supplement's tables were checked only to establish this attribution scope.
No third-party source file from those inventories is copied into this unit.
