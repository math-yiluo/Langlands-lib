# NYLL M110.011: `integralClosureValuationSubringOfMemOrInv_pullback`

Worker 194, 13 November 2026. This file proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_pullbackStatement`
with the required theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_pullback`.
The theorem conclusion is that exact target applied to all its parameters;
its source universes, section variables, explicit arguments, and instance
binders are preserved. The target's Lean/Markdown pair and imports are unchanged.

The carrier of `integralClosureValuationSubringOfMemOrInv` is
definitionally the carrier of the actual integral closure, by the published
construction and Mathlib's `ValuationSubring.ofSubring`. The initial `change`
therefore replaces membership in the constructed valuation subring by membership
in the actual integral closure.

For this equivalence, the proof then implements the same base-field integrality
argument as source M110.008, lines 194-213. Let `A` be the base valuation subring
and obtain its integral closedness locally from
`Valuation.Integers.isIntegrallyClosed` for the canonical integer subring.
An injective `A`-algebra map `K →ₐ[A] L` reflects integrality. Integral closedness
of `A` in its fraction field `K` writes the original element as an image of an
element of `A`, proving its membership. Conversely, `algebraMap_mem` puts every
element of `A` into its actual integral closure in `L`.

The original M110.011 proof, lines 255-257, invokes M110.010 and M110.008.
Those proof modules were not published at the workspace base, so this proof
uses the construction's definitional carrier equality for M110.010 and inlines
the M110.008 argument. These are local proof steps, with no second public theorem
under either adapted prerequisite name and no dependency on an unpublished
proof. The locally derived integral-closedness instance replaces the original
source's broader imports. The mathematical equivalence and hypotheses are unchanged.

The imports are the published target module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.IntegralClosureValuationSubringStatements`; and Mathlib.RingTheory.Valuation.Integral.
The proof uses Mathlib's declarations and the published construction where relevant. The proof introduces no axiom or new global instance.
The supplied field and value-group universes remain independent. This theorem
asserts exactly the stated valuation-ring property and no host reciprocity,
class-formation, cup, transfer, or Tate conclusion.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
lines 246-257; ambient context lines 21-33. Its readable retained path is
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
