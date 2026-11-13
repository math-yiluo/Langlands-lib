# NYLL M130-integer-membership: source statement targets

This module defines 1 proposition targets in
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

For an arbitrary field with a valuative relation, `𝒪[K]` is the actual
valuation integer subring. Membership is equivalent to the displayed bound
on the canonical valuation. No topology or local-field hypothesis occurs.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Valuation.lean`.
The original file SHA-256 is `6cb16ae8fea982c7f08e7d0d321806fa318e6df81fcf6b9bec6d88e93e720d0e`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Valuation.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M130.001 | `LocalFieldTheory.IsNonarchimedeanLocalField.valuation_integer_membership` | 28–30 | `valuation_integer_membershipStatement` |

## Complete propositions

### `valuation_integer_membershipStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] (x : K),
    x ∈ 𝒪[K] ↔ ValuativeRel.valuation K x ≤ 1
```


## Adaptation and reuse

Worker 202 extracted the source theorem types, prefixed the namespace with
`Langlands.NYLL`, suffixed the names with `Statement`, and moved the complete
source telescopes into their proposition bodies. The mathematical formulas,
binder kinds and order are unchanged. The original proofs and theorem attributes
(including `simp` where present) are omitted. Explicit universe parameters fix
the original order. No instance is introduced.

The imports are exactly:

- `Mathlib.Topology.Algebra.Valued.ValuativeRel`

The source norm imports and its `open DiscreteValuationField` are unnecessary
for this formula. Mathlib's `Valuation.mem_integer_iff` is the direct
membership characterization; the source writes its symmetric orientation.

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
