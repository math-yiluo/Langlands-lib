# Generic valuation-extension transport statements

This module defines two universally quantified propositions in
`Langlands.NYLL.LocalFieldTheory`. It uses Mathlib's actual
`Valuation.HasExtension` and `Valuation.IsEquiv`. Here an extension means that
the base valuation is equivalent to the comap of the extension valuation along
the supplied algebra map. Equivalence means agreement of all comparisons
`v x ≤ v y`, and allows different value monoids.

## Transport along field equivalences

`hasExtension_comap_ringEquivsStatement` quantifies over four fields
`F : Type uF`, `G : Type uG`, `F₀ : Type uF₀`, `G₀ : Type uG₀`,
with `Algebra F G` and `Algebra F₀ G₀`, and two value groups
`ΓF : Type uΓF` and `ΓG : Type uΓG`, each with
`LinearOrderedCommGroupWithZero`. All six universes are independent.

For ring equivalences `eF : F₀ ≃+* F` and `eG : G₀ ≃+* G`, the hypothesis
is the actual commuting algebra square:

```text
∀ a : F₀, eG (algebraMap F₀ G₀ a) = algebraMap F G (eF a).
```

For every `vF : Valuation F ΓF` and `vG : Valuation G ΓG` with
`vF.HasExtension vG`, the conclusion is

```text
(vF.comap eF.toRingHom).HasExtension (vG.comap eG.toRingHom).
```

Thus the equivalences point from `F₀`, `G₀` to `F`, `G`, while the comaps
pull the valuations back to `F₀`, `G₀`. The conclusion uses the quantified
`Algebra F₀ G₀`; no algebra structure is silently transported or replaced.

## Replacement by equivalent valuations

`hasExtension_of_isEquivStatement` quantifies over `F : Type uF` and
`G : Type uG` with exactly `CommRing F`, `Ring G`, and `Algebra F G`.
It separately quantifies over `ΓF : Type uΓF`, `ΓF' : Type uΓF'`,
`ΓG : Type uΓG`, and `ΓG' : Type uΓG'`, each with
`LinearOrderedCommMonoidWithZero`. These six universes are independent.

For valuations

```text
vF  : Valuation F ΓF       vF' : Valuation F ΓF'
vG  : Valuation G ΓG       vG' : Valuation G ΓG',
```

the hypotheses are `vF.HasExtension vG`, `vF.IsEquiv vF'`, and
`vG.IsEquiv vG'`, and the conclusion is `vF'.HasExtension vG'`.
The value monoids need not be groups, the rings need not be fields, and the
four value monoids are not identified.

## Original source and adaptation

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
Its SHA-256 is
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
The complete file, including both original proof bodies, was read.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M422.010, `LocalFieldTheory.hasExtension_comap_ringEquivs`, beginning at line 210 | `Langlands.NYLL.LocalFieldTheory.hasExtension_comap_ringEquivsStatement` |
| M422.011, `LocalFieldTheory.hasExtension_of_isEquiv`, beginning at line 234 | `Langlands.NYLL.LocalFieldTheory.hasExtension_of_isEquivStatement` |

The theorem signatures become the bodies of `def : Prop` declarations.
Source implicit type parameters, typeclass hypotheses, valuation parameters,
compatibility condition, and conclusions are preserved. Ordinary proof
hypotheses are written as implications. The value-type universes written
`Type*` upstream are made explicit and independent. The enclosing namespace
is prefixed with `Langlands.NYLL`; unused local-field variables, scoped
openings, and `noncomputable section` are omitted. Neither original
signature uses those local-field variables or any preceding Shrink definition.
No proof or patch from the earlier feasibility drafts is reused.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The associated supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The current Library had no `notes/errata` directory when these targets were
prepared; this records the project lookup only.

## Dependencies and scope

The sole import is `Mathlib.RingTheory.Valuation.Extension` in the approved
Lean 4.34.0 environment, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. That file defines
`Valuation.HasExtension` by its `val_isEquiv_comap` field and supplies
`Valuation.HasExtension.val_map_le_one_iff`. Its imported valuation interfaces
provide ring-equivalence comaps and `Valuation.IsEquiv`.

Searches of the current Library and Mathlib found the extension interface,
self-extension instance, and particular extension constructions, but no ready
generic result with either complete signature. Active-task searches found no
other focused M422.010–011 unit. The earlier declaration partition is a
planning source; its whole-module scheduling edges are conservative.

These are target propositions only. This module does not prove them or
construct local-field structures, small representatives, topologies, or host
models. There are no local-field, smallness, reciprocity, or model assumptions.
Proofs of the published targets are separate work.

## Attribution

The Lean file retains the original 2026 Naganori Yamaguchi copyright and
authorship, including assistance by OpenAI Codex, and records Worker 463's
namespace, import, universe, and statement-packaging changes.
The existing Apache-2.0 [LICENSE](../../../../../licenses/NYLL/LICENSE) and
full [NOTICE](../../../../../licenses/NYLL/NOTICE) remain byte-for-byte copies
of the pinned upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected source file is absent from the root NOTICE inventory and the
supplement's `ANTHROPIC_FLT_SOURCE.md` inventories; no source from those
third-party inventories is copied into this unit.
