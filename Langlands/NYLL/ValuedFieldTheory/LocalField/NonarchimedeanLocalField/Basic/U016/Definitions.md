# Valuation-integer units in the field unit group

`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits`
is the canonical homomorphism from the units of the actual valuation-integer
subring to the field units. Its full interface is

```lean
integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] :
  𝒪[K]ˣ →* Kˣ
```

The universe `u` is arbitrary. The domain `𝒪[K]` is the valuation-integer subring
of the caller's supplied valuative relation. No topology, nontriviality,
local compactness or local-field assumption is required. The homomorphism is
`Units.map (algebraMap 𝒪[K] K).toMonoidHom`. It uses Mathlib's canonical algebra
map of the valuation subring; `Units.map` supplies the preservation laws.
There is no new field embedding, chosen valuation or global instance.

## Source correspondence and modifications

| Source unit and original name | Adapted name |
| --- | --- |
| M128.016, `LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits`, lines 182–184 | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits` |

The source is `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
its SHA-256 is `c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.
The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, retained under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered original is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project notes.

The extraction preserves the original definition body, explicit `K`, independent
universe and both instance parameters. It prefixes the namespace with
`Langlands.NYLL`, keeps only this source command, omits the unused `WithZero`
scoped opening, and adds the modification notice and focused module description.
The original sole import `Mathlib.NumberTheory.LocalField.Basic` is retained.
All data and constructor laws are obtained directly from `algebraMap` and
`Units.map`; this alias supplies the source spelling used by later port units.

A successful focused Lean-service check compiled the extraction with that
Mathlib import and no other NYLL dependency. Thus the earlier normalized
valuation and its laws M128.001–015 are not prerequisites of this definition.
The published M128.001 valuation `v` is reused separately when needed; it is
not duplicated here. The subsequent evaluation, injectivity and valuation-zero
theorems are separate targets and proofs. This file constructs only the map.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The unchanged Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) accompany this
subset at `licenses/NYLL/`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
These bytes were verified against the carried-license manifest. The original
NOTICE has no source-specific entry for this extracted file. Worker 120 made
the recorded extraction and namespace/import changes on 9 November 2026;
no earlier adaptation or patch10 code is incorporated.
