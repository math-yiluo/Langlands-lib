# NYLL M106-transport-laws: source statement targets

This module defines 3 proposition targets in
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u v w` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

The first target equates the actual subgroups of units forming the value
groups of `v` and its comap. The other two targets use the exact
`valuationSubringRingEquivOfComap` construction and the canonical
maximal ideals of the two valuation subrings. No discrete-rank,
completeness, topology or local-field hypothesis is added.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationTransport.lean`.
The original file SHA-256 is `173bac49cc97f73e78074fce0bd629dc212ad06dd0ead5f0348e76be9a045890`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationTransport.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M106.001 | `ValuationTheory.DiscreteValuationField.Valuation.valueGroup_comap_ringEquiv` | 32–36 | `valueGroup_comap_ringEquivStatement` |
| M106.005 | `ValuationTheory.DiscreteValuationField.Valuation.valuationSubringRingEquivOfComap_mem_maximalIdeal_iff` | 122–128 | `valuationSubringRingEquivOfComap_mem_maximalIdeal_iffStatement` |
| M106.007 | `ValuationTheory.DiscreteValuationField.Valuation.maximalIdeal_comap_valuationSubringRingEquivOfComap` | 160–167 | `maximalIdeal_comap_valuationSubringRingEquivOfComapStatement` |

## Complete propositions

### `valueGroup_comap_ringEquivStatement`

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L]
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
(v : _root_.Valuation K Γ) (e : L ≃+* K),
    MonoidWithZeroHom.valueGroup
        (.ofClass (v.comap (e : L →+* K))) =
      MonoidWithZeroHom.valueGroup (.ofClass v)
```

### `valuationSubringRingEquivOfComap_mem_maximalIdeal_iffStatement`

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L]
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
(v : _root_.Valuation K Γ) (e : L ≃+* K)
    (x : (v.comap (e : L →+* K)).valuationSubring),
    valuationSubringRingEquivOfComap v e x ∈
        IsLocalRing.maximalIdeal v.valuationSubring ↔
      x ∈ IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring
```

### `maximalIdeal_comap_valuationSubringRingEquivOfComapStatement`

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L]
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
(v : _root_.Valuation K Γ) (e : L ≃+* K),
    (IsLocalRing.maximalIdeal v.valuationSubring).comap
        (valuationSubringRingEquivOfComap v e :
          (v.comap (e : L →+* K)).valuationSubring →+*
            v.valuationSubring) =
      IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring
```


## Adaptation and reuse

Worker 202 extracted the source theorem types, prefixed the namespace with
`Langlands.NYLL`, suffixed the names with `Statement`, and moved the complete
source telescopes into their proposition bodies. The mathematical formulas,
binder kinds and order are unchanged. The original proofs and theorem attributes
(including `simp` where present) are omitted. Explicit universe parameters fix
the original order. No instance is introduced.

The imports are exactly:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport.Definitions`

The data construction is in the companion `Definitions` pair. It is staged
separately before this statement pair. The source section context at
lines 27–28 supplies the complete field/value-group telescope.

The published Library and approved Mathlib were searched for these exact
targets before authoring; none already declares these targets. Reused data is
imported by its published Lean name. No other worker's draft is copied.

## Attribution

The original copyright and author header is retained verbatim. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain in the Library, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public partition reports no patch10 modification for this module.
This support unit asserts no host reciprocity, Tate, cup-product, transfer or
class-formation result.
