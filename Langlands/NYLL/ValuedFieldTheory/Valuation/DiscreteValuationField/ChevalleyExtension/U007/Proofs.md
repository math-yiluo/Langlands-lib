# NYLL M110.007: `integralClosure_mem_valuationSubring_of_hasExtension`

Worker 194, 13 November 2026. This file proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosure_mem_valuationSubring_of_hasExtensionStatement`
with the required theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosure_mem_valuationSubring_of_hasExtension`.
The theorem conclusion is that exact target applied to all its parameters;
its source universes, section variables, explicit arguments, and instance
binders are preserved. The target's Lean/Markdown pair and imports are unchanged.

The element's subtype property gives integrality over the base valuation ring.
`IsIntegral.tower_top` transports this to integrality over the extending valuation
ring, using Mathlib's canonical subring algebra and scalar tower supplied by
`Valuation.HasExtension`. `Valuation.Integers.mem_of_integral`, applied to the
valuation's own integer subring, then gives membership in `vL.valuationSubring`.
The proof follows the original proof at lines 175-180, with the first intermediate
term written on one line. No other NYLL proof is used.

The imports are the published target module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.IntegralClosureStatements`; and Mathlib.RingTheory.Valuation.Integral.
The proof uses Mathlib's declarations and the published construction where relevant. The proof introduces no axiom or new global instance.
The supplied field and value-group universes remain independent. This theorem
asserts exactly the stated valuation-ring property and no host reciprocity,
class-formation, cup, transfer, or Tate conclusion.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
lines 170-180; ambient context lines 21-33. Its readable retained path is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`.
The original file SHA-256 is
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
also `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Copyright 2026 Naganori Yamaguchi; original authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original header is retained with an explicit
modification record. The namespace is prefixed by `Langlands.NYLL`; the
upstream import closure and unused residue-field namespace are replaced by the
focused published target import. The implementation adaptations are described
above. Unchanged license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
Development compilation does not constitute independent proof acceptance;
publication requires the proof policy's independent review, build, and exact-target checks.
