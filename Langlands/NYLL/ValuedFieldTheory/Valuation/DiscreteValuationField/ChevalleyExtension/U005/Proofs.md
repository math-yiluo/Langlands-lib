# Exact pullback of valuation subrings from `HasExtension` (NYLL M110.005)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuationStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has implicit fields `K : Type u`, `L : Type v` with
`[Field K] [Field L] [Algebra K L]`, implicit `ΓK : Type w` with
`[LinearOrderedCommGroupWithZero ΓK]`, explicit `vK : Valuation K ΓK` and
`B : ValuationSubring L`, the instance argument `[vK.HasExtension B.valuation]`,
and explicit `x : K`. Its type is
`valuationSubring_pullback_of_hasExtension_valuationStatement vK B x`, which
unfolds to `algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring`.

Mathematically: if the canonical valuation of the valuation ring `B` of `L`
extends `vK` (Mathlib's `Valuation.HasExtension`, i.e. its restriction to `K` is
equivalent to `vK`), then `B ∩ K = O_v`, checked elementwise.

## Implemented proof

After `unfold valuationSubring_pullback_of_hasExtension_valuationStatement` the
rest is the unchanged source tactic proof, one chain of three equivalences in
each direction:

`algebraMap K L x ∈ B` ⇔ `B.valuation (algebraMap K L x) ≤ 1`
(`ValuationSubring.valuation_le_one_iff`) ⇔ `vK x ≤ 1`
(`Valuation.HasExtension.val_map_le_one_iff vK B.valuation x`, using the
instance) ⇔ `x ∈ vK.valuationSubring` (Mathlib's `Valuation.mem_valuationSubring_iff`).

Dependencies are Mathlib only (`Mathlib/RingTheory/Valuation/Extension.lean` and
`Mathlib/RingTheory/Valuation/ValuationSubring.lean`); no auxiliary declaration,
instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean:135–151`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean#L135-L151)
(partition unit lines 135–154; docstring at lines 133–134).

| Original (namespace `ValuationTheory.DiscreteValuationField.Valuation`) | Adapted |
| --- | --- |
| Theorem `valuationSubring_pullback_of_hasExtension_valuation`, lines 135–151 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion, line 138 | `valuationSubring_pullback_of_hasExtension_valuationStatement vK B x` |
| Tactic proof, lines 139–151 | Identical, preceded by one `unfold` |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source imports; omission of the unused universes
`x y z`, the `noncomputable section` and the unused `ResidueField` open.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 133's dated modification record. Worker 133 extracted
this proof directly from the pinned original and the frozen statement module;
there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`, recomputed by
Worker 133 on 13 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m110)
lists this unit in module M110 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
