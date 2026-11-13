# `HasExtension` from exact pullback of valuation subrings (NYLL M110.004)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullbackStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has implicit fields `K : Type u`, `L : Type v` with
`[Field K] [Field L] [Algebra K L]`, implicit `ΓK : Type w` with
`[LinearOrderedCommGroupWithZero ΓK]`, and explicit `vK : Valuation K ΓK`,
`B : ValuationSubring L` and
`hpullback : ∀ x : K, algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring`.
Its type is
`hasExtension_valuation_of_valuationSubring_pullbackStatement vK B hpullback`,
which unfolds to `vK.HasExtension B.valuation`.

Mathematically: if the valuation ring `B` of `L` satisfies `B ∩ K = O_v`, then
the canonical valuation of `B` (with values in `ValuationSubring.ValueGroup`)
restricts on `K` to a valuation equivalent to `vK`, i.e. Mathlib's
`Valuation.HasExtension vK B.valuation` holds.

## Implemented proof

After `unfold hasExtension_valuation_of_valuationSubring_pullbackStatement` the
rest is the unchanged source tactic proof. Mathlib's
`Valuation.HasExtension.ofComapInteger` (`Mathlib/RingTheory/Valuation/Extension.lean`)
reduces the goal to `B.valuation.integer.comap (algebraMap K L) = vK.integer`,
proved by `le_antisymm`:

* `⊆`: if `B.valuation (algebraMap K L x) ≤ 1`, then
  `ValuationSubring.mem_of_valuation_le_one` puts the image in `B`,
  `hpullback` gives `x ∈ vK.valuationSubring`, and
  `Valuation.mem_valuationSubring_iff` with `Valuation.mem_integer_iff` gives
  `x ∈ vK.integer`;
* `⊇`: conversely `x ∈ vK.integer` gives `x ∈ vK.valuationSubring` by the same
  two iff lemmas, `hpullback` puts `algebraMap K L x` in `B`, and
  `ValuationSubring.valuation_le_one_iff` gives `B.valuation (algebraMap K L x) ≤ 1`.

As the task context notes, `vK.mem_valuationSubring_iff` is Mathlib's
`Valuation.mem_valuationSubring_iff`, not an NYLL lemma. Dependencies are
Mathlib only; no auxiliary declaration, instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean:113–131`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean#L113-L131)
(partition unit lines 113–134; docstring at lines 111–112).

| Original (namespace `ValuationTheory.DiscreteValuationField.Valuation`) | Adapted |
| --- | --- |
| Theorem `hasExtension_valuation_of_valuationSubring_pullback`, lines 113–131 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `vK.HasExtension B.valuation` (line 117) | `hasExtension_valuation_of_valuationSubring_pullbackStatement vK B hpullback` |
| Tactic proof, lines 118–131 | Identical, preceded by one `unfold` |

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
