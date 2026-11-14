# NYLL M103 DVF Basic: source statement targets

This module defines six proposition targets in
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`, adapted from
theorems of Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean)
(inventory module M103). Each target is a closed `def : Prop`; its source
parameters are universally quantified inside the proposition in their original
order and with their original explicit, implicit and instance binder kinds.
Universe parameters `u v` are arbitrary and retain the source order: the field
`K` lives in `Type u` and the value group of the chosen valuation in `Type v`.
This file supplies statements only; their proofs require separate
`lean.proof@1` tasks.

Throughout, `F : DVF.{u, v} K` is a field `K` with a chosen valuation
`F.valuation : Valuation K F.ValueGroup` of discrete rank one, as in the
published `Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`.
`F.valuationSubring` is the subtype of `x : K` with `F.valuation x ≤ 1`, with
Mathlib's canonical ring, domain and local-ring instances, and
`F.maximalIdeal` is its maximal ideal. Mathlib's
`F.valuation.IsUniformizer x` means `F.valuation x` equals the chosen generator
`< 1` of the value group of `F.valuation`.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`.
The original file SHA-256 is
`abda99fd0b28655e1317ae832e8c94c7431b7229d99cf07138d89c4a5c953493`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The section variables `{K : Type u} [Field K]` are declared at source line 51.
The table gives each source theorem and the lines containing its complete type
(including the proof delimiter `:=`); the original name is relative to
`ValuationTheory.DiscreteValuationField.DVF` and the adapted target to
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF`.

| Unit | Original theorem | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M103.011 | `valuationSubring_isDiscreteValuationRing` | 90–91 | `valuationSubring_isDiscreteValuationRingStatement` |
| M103.015 | `mem_valuationSubring_iff` | 113–114 | `mem_valuationSubring_iffStatement` |
| M103.020 | `exists_uniformizer` | 149–150 | `exists_uniformizerStatement` |
| M103.021 | `uniformizer_mem_maximalIdeal` | 156–158 | `uniformizer_mem_maximalIdealStatement` |
| M103.030 | `maximalIdeal_ne_bot` | 304–305 | `maximalIdeal_ne_botStatement` |
| M103.039 | `MaximalIdealPowSuccQuot.inductionOn` (protected) | 389–395 | `MaximalIdealPowSuccQuot.inductionOnStatement` (protected) |

## Complete propositions

### `valuationSubring_isDiscreteValuationRingStatement` (M103.011)

```lean
∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K),
    IsDiscreteValuationRing F.valuationSubring
```

The valuation subring of every chosen discrete valuation field is a discrete
valuation ring in Mathlib's sense.

### `mem_valuationSubring_iffStatement` (M103.015)

```lean
∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K) (x : K),
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1
```

An element `x : K` lies in Mathlib's valuation subring of `F.valuation`
exactly when its valuation is at most one.

### `exists_uniformizerStatement` (M103.020)

```lean
∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K),
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K))
```

Some element of the valuation subring is a uniformizer of `F.valuation`.

### `uniformizer_mem_maximalIdealStatement` (M103.021)

```lean
∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)),
    pi ∈ F.maximalIdeal
```

Every uniformizer in the valuation subring lies in its maximal ideal.

### `maximalIdeal_ne_botStatement` (M103.030)

```lean
∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K),
    F.maximalIdeal ≠ ⊥
```

The maximal ideal of the valuation subring is nonzero.

### `MaximalIdealPowSuccQuot.inductionOnStatement` (M103.039)

```lean
∀ {K : Type u} [Field K]
    (F : DVF.{u, v} K) (n : ℕ)
    {motive : F.MaximalIdealPowSuccQuot n → Prop}
    (q : F.MaximalIdealPowSuccQuot n)
    (h : ∀ a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u),
      motive (F.maximalIdealPowSuccQuotMk n a)),
    motive q
```

A predicate on the successive quotient `m^n / m^(n+1)` holds for every class
`q` once it holds for the image of every `a ∈ m^n` under the quotient map.
`MaximalIdealPowSuccQuot` and `maximalIdealPowSuccQuotMk` are the definitions
of source units M103.032 and M103.036, published in the sibling module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic.Definitions`.

## Adaptation and reuse

Worker 171 made the following modifications on 14 November 2026. The source
theorem types are extracted, the namespace is prefixed with
`Langlands.NYLL`, the names receive the suffix `Statement`, and the complete
source telescopes (the section variables `{K : Type u} [Field K]` followed by
the theorem's own binders) are moved into the proposition bodies. The
mathematical formulas, binder names, binder kinds and order are unchanged. The
source `protected` modifier of M103.039 is kept on its target. The original
proofs are omitted. Explicit universe parameters `.{u, v}` fix the source
universe order. No instance is introduced. `set_option
linter.unusedVariables false in` precedes the targets of M103.021 and M103.039
only to silence the linter for the source hypothesis names `hpi` and `h`, which
the conclusion does not mention; it does not change the propositions. Short
docstrings stating the source unit are added.

The imports are exactly:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic.Definitions`,
  which supplies `MaximalIdealPowSuccQuot` and `maximalIdealPowSuccQuotMk` for
  M103.039 and imports the published stem module with `DVF`,
  `valuationSubring` and `maximalIdeal`.

As a fidelity check (not part of this publication), each original source proof
was replayed unchanged against its target in a private scratch module and
compiled; this confirms that each body is the source statement. The published
Library and approved Mathlib were searched for these exact targets before
authoring; none already declares them. Mathlib's
`Valuation.valuationSubring_isDiscreteValuationRing`,
`Valuation.mem_valuationSubring_iff`,
`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial` and
`Submodule.Quotient.induction_on` are the results the source proofs use; they
are stated for Mathlib's valuation subring and quotient types, not for these
`DVF` abbreviations and the `def` `MaximalIdealPowSuccQuot`, so the targets are
published as statements. No other worker's draft is copied.

## Attribution

The original copyright and author header is retained verbatim. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain in the Library, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean file's second header comment records the modifications. The public
partition reports no patch10 modification for this module. This support unit
asserts no host reciprocity, Tate, cup-product, transfer or class-formation
result.
