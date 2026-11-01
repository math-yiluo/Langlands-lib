# Valuation-ring preservation from unique extension

This module proves
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension`.
Its complete type is the published closed proposition
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.MemValuationSubringAlgEquivIffOfHasUniqueValuationExtensionStatement.{u, v, w, x}`,
imported from
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.AutomorphismStatement`.
The theorem has no mathematical declaration parameters outside that proposition.

## Exact target and universes

Writing `DVF` for the existing
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`, the proposition
expands to:

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : DVF.{u, v} K} {target : DVF.{w, x} L}
  [base.valuation.HasExtension target.valuation]
  (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
  (σ : L ≃ₐ[K] L) (z : L),
  z ∈ target.valuation.valuationSubring ↔
    σ z ∈ target.valuation.valuationSubring
```

The four levels remain independent: `u` and `w` are the base and target field
carrier universes; `v` and `x` are their chosen value-group universes.
The imported uniqueness predicate has five universe parameters, specialized
here exactly to `u, v, w, x, x`. Its comparison value group lives in `Type x`,
which includes the chosen target's value group. No level is fixed to zero.
The proof introduces all binders in the published order and adds no premise.

`HasExtension` uses the actual `algebraMap K L` supplied by `[Algebra K L]`.
The uniqueness predicate alone does not assert that the chosen target extends
the base, so the separate extension premise is retained and used. The chosen
subring is Mathlib's `target.valuation.valuationSubring`, whose membership
means `target.valuation z ≤ 1`. The conclusion retains the original direction:
membership of `z` if and only if membership of `σ z`.

## Implemented proof

Set `vσ := target.valuation.comap (σ : L →+* L)`. This is a valuation on the
same field `L` with the same chosen target value group in universe `x`.
Obtain a local instance `base.valuation.HasExtension vσ` by applying the
published
`Langlands.NYLL.LocalFieldTheory.hasExtension_comap_ringEquivs`, imported
from
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExtensionTransportProof`.
Its two pairs of fields are both the supplied `K, L`; its base equivalence is
`RingEquiv.refl K`, and its target equivalence is `σ.toRingEquiv`.
The required commuting square is precisely
`σ.commutes a : σ (algebraMap K L a) = algebraMap K L a`.
Changing the identity equivalence's ring homomorphism to `RingHom.id K` and
using `Valuation.comap_id` removes the base comap. Both algebra structures
in the generic theorem are the original supplied algebra, and its original
extension premise is the supplied instance.

Apply `huniq vσ` using this local instance to obtain
`target.valuation.IsEquiv vσ`. Mathlib's
`Valuation.isEquiv_iff_valuationSubring` converts this to
`target.valuation.valuationSubring = vσ.valuationSubring`.
Definitionally, membership of `z` in `vσ.valuationSubring` is membership of
`σ z` in the chosen target subring. The final `change` expresses that fact,
and rewriting by the subring equality closes the iff.

The instance exists only inside this proof. The module adds just the one
theorem; it introduces no global instance, helper target or duplicate
M304.002 transport theorem. All imported Lean/Markdown pairs remain unchanged.
No finite-dimensionality, completeness, separability, Galois or preservation
hypothesis is required.

## Original correspondence

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`, lines 70–86](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean#L70-L86).
The complete file has SHA-256
`9eb843515be4be35872451b0d71a3c84a614678ef39b3b577cec6f90f1fa0f45`.
Lines 1–110, including the complete theorem and its context, were read for
this adaptation.

| Original at the pinned commit | Implemented adaptation |
| --- | --- |
| Universes, namespaces and supplied fields, lines 33–41 | Retain the four used universe levels and add the `Langlands.NYLL` namespace prefix; introduce the supplied fields and instances from the closed target. |
| M304.003 signature, lines 70–76 | State the theorem with exactly the published closed proposition as its complete type; introduce its original hypotheses, automorphism and element. |
| Pulled-back valuation, line 77 | Keep the same local valuation `vσ`. |
| Local extension instance via M304.002, lines 78–80 | Specialize the existing generic transport theorem using the identity base equivalence and `σ.commutes`; simplify the identity comap. |
| Uniqueness and valuation-subring equality, lines 81–84 | Use `huniq vσ` and `Valuation.isEquiv_iff_valuationSubring` with the same order of valuations. |
| Membership conversion and rewrite, lines 85–86 | Keep the same definitional `change` and equality rewrite. |

The correct source split is signature **70–76**, proof **77–86**. The frozen
statement pair's line-split imprecision is left unchanged. The published
generic transport replaces the original helper at lines 56–66 rather than
porting that helper again. The source partition records no patch10 change for
M304.

## Attribution and modifications

Worker 1199 wrote this adaptation and its explanation on 1 November 2026.
Worker 106 contributed the identity-base/automorphism specialization and proof
route. The proof keeps the original uniqueness-to-subring-equality argument,
replaces upstream imports with the published target and generic transport
proof, prefixes the namespace, introduces the closed target's binders inside
the proof, and omits unused source context, the fifth universe,
`noncomputable section` and pointwise scope. The source hypotheses and
conclusion are unchanged.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained: copyright 2026 Naganori
Yamaguchi, all rights reserved; authors Naganori Yamaguchi (assisted by OpenAI
Codex). The source is Apache-2.0. The existing verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused without edits.
The original NOTICE has no entry for `RealLowerGroups.lean`.
The applicable workspace, project and current-Library errata directories were
absent when this proof was prepared.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. This proves the general chosen
valuation-ring preservation lemma. Integral automorphisms, real ramification
filtrations, host inertia and finite Type 0 reciprocity remain separate units.
