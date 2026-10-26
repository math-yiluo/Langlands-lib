# Generic valuation-extension transport proofs

This module proves the two complete published propositions imported from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExtensionTransportStatement`.
The theorems have exactly those proposition definitions as their types and
introduce all their quantified parameters inside the proof.

| Proof declaration in `Langlands.NYLL.LocalFieldTheory` | Published target in the same namespace |
| --- | --- |
| `hasExtension_comap_ringEquivs` | `hasExtension_comap_ringEquivsStatement` |
| `hasExtension_of_isEquiv` | `hasExtension_of_isEquivStatement` |

For the first theorem, the four field universes and the two value-group
universes remain independent. The supplied ring equivalences point from
`F₀` and `G₀` to `F` and `G`. The pointwise commuting square uses the supplied
algebra structures on both pairs of fields. The conclusion pulls the
valuations back along those equivalences, with exactly the comap directions
specified by the published target.

For the second theorem, the assumptions remain exactly a commutative base
ring `F`, a ring algebra `G`, and four independently universed linearly ordered
commutative value monoids with zero. Neither fields nor value groups are
required. The two ring universes are independent as well.

## Implemented proofs

For `hasExtension_comap_ringEquivs`, construct `Valuation.HasExtension` by
proving its `val_isEquiv_comap` field. Apply
`Valuation.isEquiv_iff_val_le_one` to reduce valuation equivalence over the
field `F₀` to agreement of comparisons with one. At `a : F₀`, unfolding comap
evaluation gives

```text
vF (eF a) ≤ 1 ↔ vG (eG (algebraMap F₀ G₀ a)) ≤ 1.
```

Rewrite the right side using the supplied commuting square. The result is
the reverse of `Valuation.HasExtension.val_map_le_one_iff vF vG (eF a)`.

For `hasExtension_of_isEquiv`, again construct the single class field. For
arbitrary `x y : F`, compose the comparison equivalence from `vF'` to `vF`
given by the reverse of `hF`, the original extension equivalence from `vF`
to the algebra-map comap of `vG`, and `hG` at the two algebra-map images.
The final comparison is exactly the comap of `vG'`. This proof works with
value monoids because it uses only comparison equivalence and transitivity.

No helpers, new instances or additional premises are introduced. The imported
statement pair and all its dependencies are unchanged.

## Source, adaptation and attribution

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The complete original file was read; its SHA-256 is
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
M422.010 occupies lines 210–229 and M422.011 lines 234–253.
The two implemented proof bodies retain these original routes.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The scoped Library and project `notes/errata` directory lookups were absent
when this proof unit was prepared.

Worker 586 prefixes the namespace with `Langlands.NYLL`, replaces the original
imports with the published statement module, and adds introductions for the
full proposition targets. Unused local-field context, scoped openings and
`noncomputable section` are omitted. No proof or compatibility patch from a
feasibility draft is reused. Importing the accepted statement module is the
only dependency on earlier project adaptations.

The Lean file retains the original 2026 Naganori Yamaguchi copyright and
authorship, including assistance by OpenAI Codex. The existing Apache-2.0
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) are reused without edits.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected source is absent from the root NOTICE's file inventory.

## Scope

These are generic valuation-extension transport proofs. They do not construct
small models, transported local-field structures, Artin maps, host reciprocity
or Weil systems. Their approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
