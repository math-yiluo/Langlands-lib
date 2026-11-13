# NYLL M128-valuation-laws: source statement targets

This module defines 6 proposition targets in
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

The valuation is the published `v` obtained by transporting the canonical
valuation through Mathlib's `valueGroupWithZeroIsoInt` and taking the
exponent. Its sign is unchanged. The last target uses the actual inclusion
`integerUnitsToFieldUnits : 𝒪[K]ˣ →* Kˣ`. The six complete source hypotheses
include a field, valuative relation, topology and local-field certificate
on one arbitrary universe; no compatibility premise has been added.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`.
The original file SHA-256 is `c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M128.002 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_apply` | 42–50 | `v_applyStatement` |
| M128.003 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_surjective` | 54–56 | `v_surjectiveStatement` |
| M128.004 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_mul` | 73–76 | `v_mulStatement` |
| M128.005 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_one` | 81–83 | `v_oneStatement` |
| M128.006 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_inv` | 98–100 | `v_invStatement` |
| M128.019 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits` | 206–208 | `v_integerUnitsToFieldUnitsStatement` |

## Complete propositions

### `v_applyStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
    v K x =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
          ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
            ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Additive.toMul x).ne_zero)))
```

### `v_surjectiveStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Function.Surjective (v K)
```

### `v_mulStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ),
    v K (Additive.ofMul (x * y)) =
      v K (Additive.ofMul x) + v K (Additive.ofMul y)
```

### `v_oneStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    v K (Additive.ofMul (1 : Kˣ)) = 0
```

### `v_invStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ),
    v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x)
```

### `v_integerUnitsToFieldUnitsStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ),
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0
```


## Adaptation and reuse

Worker 202 extracted the source theorem types, prefixed the namespace with
`Langlands.NYLL`, suffixed the names with `Statement`, and moved the complete
source telescopes into their proposition bodies. The mathematical formulas,
binder kinds and order are unchanged. The original proofs and theorem attributes
(including `simp` where present) are omitted. Explicit universe parameters fix
the original order. No instance is introduced.

The imports are exactly:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`

The source's Mathlib import is available through the published definitions.
The original `v` and integer-unit inclusion are reused without alteration.
The explicit root qualification on Mathlib's local-field isomorphism is retained.

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
