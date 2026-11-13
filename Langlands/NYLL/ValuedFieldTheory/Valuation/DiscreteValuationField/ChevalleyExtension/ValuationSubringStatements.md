# NYLL M110: domination, pullback and valuation-overring targets

The pinned original is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`.
The readable source is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`.
The exact Lean file SHA-256 is
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
the source snapshot is also recorded by
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Copyright 2026 Naganori Yamaguchi; original authors Naganori Yamaguchi
(assisted by OpenAI Codex). The source header is retained in the Lean file.
The unchanged upstream license and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 194 extracted and namespaced this unit on 13 November 2026.

The source context is at lines 21-33: namespace
`ValuationTheory.DiscreteValuationField.Valuation`, a noncomputable section,
universes `u v w x y z`, then
`{K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]`,
`{ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]`.
The port retains that context in the same order. Lean generalizes the used
section parameters and retains all declaration-local binders. Unused source
universe names are not artificial extra universe parameters on declarations.

| Unit | Original declaration | Signature lines | Full source command | Adapted declaration |
| --- | --- | --- | --- | --- |
| M110.002 | `ValuationTheory.DiscreteValuationField.Valuation.mem_base_valuationSubring_of_lift_mem` | 47-54 | 47-76 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.mem_base_valuationSubring_of_lift_memStatement` |
| M110.003 | `ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring` | 86-94 | 86-109 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubringStatement` |
| M110.004 | `ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback` | 113-117 | 113-131 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullbackStatement` |
| M110.005 | `ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation` | 135-138 | 135-151 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuationStatement` |
| M110.017 | `ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal` | 376-380 | 376-408 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement` |

- `mem_base_valuationSubring_of_lift_memStatement`: Local domination forces a lifted base-field element back into the base valuation ring.
- `exists_extension_valuationSubringStatement`: There exists a dominating valuation subring of the actual extension field with exact base-field pullback.
- `hasExtension_valuation_of_valuationSubring_pullbackStatement`: Exact pullback implies extension for the canonical valuation of the target subring.
- `valuationSubring_pullback_of_hasExtension_valuationStatement`: An installed extension to a canonical subring valuation gives pointwise exact pullback.
- `valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement`: An overring equals the smaller valuation ring when its localization center is the smaller maximal ideal.

Each adapted declaration is a `def` returning `Prop`, with precisely the
source theorem's generalizing section parameters and declaration-local binder
order and kinds. Its body is the source conclusion; its theorem proof is
omitted. Source hypotheses remain arguments of the definition, including named
proof arguments that do not occur in the conclusion. No `simp` attribute is
transferred to a proposition definition. The declarations specify proof targets;
this file publishes no proofs of those targets.

The original imports through NYLL's `ValuationExtension` are replaced by
focused Mathlib imports. No requested statement uses the upstream DVF packages,
residue-field namespace, or any unpublished declaration from another NYLL
module, so those dependencies and the unused `open` command are omitted.
Mathlib supplies the actual valuation subrings, canonical valuations,
`Valuation.HasExtension`, algebras, local rings, ideals and scalar towers.
No global instance or axiom is introduced. The namespace is prefixed by
`Langlands.NYLL`; the source spelling of `_root_.Valuation` is retained to
avoid resolving it to the source's `Valuation` namespace.

The imports are `Mathlib.RingTheory.Valuation.Extension`,
`Mathlib.RingTheory.DedekindDomain.IntegralClosure` and
`Mathlib.RingTheory.Valuation.LocalSubring`. M110.002 retains the explicit
`hB`, `hlocal`, implicit `{x : K}` and explicit `hxB`, in that order.
M110.003 retains the dependent witness `hB` for the codomain-restricted ring
homomorphism. M110.004 retains explicit `hpullback`; M110.005 retains its
instance binder `[vK.HasExtension B.valuation]`. M110.017 has only the
ambient `{L : Type v} [Field L]` section parameters and the explicit `R S`,
`hRS`, `hcenter`; no unused base field, algebra or value group is added.
All conclusions in this file are copied unchanged. The additional comments,
namespace, focused imports, and replacement of theorem/proof by proposition
body are the complete modification list.

The environment for focused checks is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
The full closed declaration functions are compared definitionally in a private
source-signature check, and each target is separately inspected as returning
`Prop`. Compilation and inspection are development checks; these targets
retain independent semantic review and separate future proof obligations.
None asserts a host reciprocity, class-formation, cup, transfer or Tate result.
