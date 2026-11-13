# NYLL M135-maximal-ideal-actions: source statement targets

This module defines 4 proposition targets in
`Langlands.NYLL.LocalFieldTheory`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

Here `𝓂[K]` is Mathlib's maximal ideal of the actual valuation integer ring.
Each equivalence is an arbitrary ring automorphism of that ring. The powers
include `n = 0`. The targets need no topology, discrete valuation, local-field
certificate, Galois action or principal-unit quotient.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean`.
The original file SHA-256 is `42c0bc7ef0a080024990e1d4f323703c5e8965cb3fce29074318d4ab2bf82194`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M135.001 | `LocalFieldTheory.integerRingEquiv_mem_maximalIdeal` | 24–27 | `integerRingEquiv_mem_maximalIdealStatement` |
| M135.002 | `LocalFieldTheory.integerRingEquiv_map_maximalIdeal` | 32–35 | `integerRingEquiv_map_maximalIdealStatement` |
| M135.003 | `LocalFieldTheory.integerRingEquiv_map_maximalIdeal_pow` | 50–54 | `integerRingEquiv_map_maximalIdeal_powStatement` |
| M135.004 | `LocalFieldTheory.integerRingEquiv_mem_maximalIdeal_pow` | 58–61 | `integerRingEquiv_mem_maximalIdeal_powStatement` |

## Complete propositions

### `integerRingEquiv_mem_maximalIdealStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (x : 𝒪[K]),
    e x ∈ (𝓂[K] : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] : Ideal 𝒪[K])
```

### `integerRingEquiv_map_maximalIdealStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]),
    Ideal.map e.toRingHom (𝓂[K] : Ideal 𝒪[K]) = (𝓂[K] : Ideal 𝒪[K])
```

### `integerRingEquiv_map_maximalIdeal_powStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat),
    Ideal.map e.toRingHom (𝓂[K] ^ n : Ideal 𝒪[K]) =
      (𝓂[K] ^ n : Ideal 𝒪[K])
```

### `integerRingEquiv_mem_maximalIdeal_powStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    (e : 𝒪[K] ≃+* 𝒪[K]) (n : Nat) (x : 𝒪[K]),
    e x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) ↔ x ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
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
- `Mathlib.RingTheory.Ideal.Operations`

The source's principal-unit quotient import is replaced by the two Mathlib
imports supplying the concrete rings, ideals, map and powers. The earlier
source principal-unit constructions do not occur in these formulas.

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
