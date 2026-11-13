# NYLL M110.012: `integralClosureValuationSubringOfMemOrInv_hasExtension`

Worker 194, 13 November 2026. This file proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtensionStatement`
with the required theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension`.
The theorem conclusion is that exact target applied to all its parameters;
its source universes, section variables, explicit arguments, and instance
binders are preserved. The target's Lean/Markdown pair and imports are unchanged.

Let `B` be the constructed integral-closure valuation subring. The local
`hpullback` proof establishes exact pullback of its carrier to the base valuation
ring. Membership in `B` is definitionally membership in the actual integral
closure. The forward implication reflects integrality through the injective
`vK.valuationSubring`-algebra homomorphism from `K` to `L` and uses integral
closedness of the base valuation ring in its fraction field. That integral
closedness is derived locally from the canonical valuation-integers theorem.
The reverse implication is `algebraMap_mem` for the actual integral closure.
This is the argument of source M110.008, lines 194-213, together with the
definitional membership step underlying M110.010 and M110.011.

Mathlib's `Valuation.HasExtension.ofComapInteger` reduces the desired extension
property to equality between the inverse image of `B.valuation.integer` and
`vK.integer`. `ValuationSubring.integer_valuation` identifies the former integer
ring with `B.toSubring`; subring extensionality then reduces the equality to the
local `hpullback` equivalence. Membership in `vK.integer` and in
`vK.valuationSubring` is definitionally the same.

The source M110.012 proof, lines 269-272, invokes M110.004 (lines 110-131)
and M110.011 (lines 246-257). These prerequisite proof modules were not
published at the workspace base, so the implementation keeps their mathematical
arguments local and introduces no duplicate public prerequisite theorem.
Using `integer_valuation` compresses the source M110.004 proof's explicit
two-inclusion argument into subring extensionality. The theorem still supplies
exactly the canonical valuation's `HasExtension` property, under the supplied
valuative dichotomy; it does not prove that dichotomy or assume it implicitly.

The imports are the published target module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.IntegralClosureValuationSubringStatements`; and Mathlib.RingTheory.Valuation.Integral.
The proof uses Mathlib's declarations and the published construction where relevant. The proof introduces no axiom or new global instance.
The supplied field and value-group universes remain independent. This theorem
asserts exactly the stated valuation-ring property and no host reciprocity,
class-formation, cup, transfer, or Tate conclusion.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
lines 262-272; ambient context lines 21-33. Its readable retained path is
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
