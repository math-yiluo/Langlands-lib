# NYLL M129-norm-value-inverses: source statement targets

This module defines 2 proposition targets in
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u v` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

These equations hold in the actual base integer ring. The two field universes
are independent. `LocalFieldTheory.ValuativeExtension` resolves to the published
`Langlands.NYLL.LocalFieldTheory.ValuativeExtension`, whose field records
integrality of extension integers. It is not Mathlib's root valuative-extension
class. There is no finite-dimensionality or local-field premise.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`.
The original file SHA-256 is `0e9e3d68b6d964addae89ea2185146fdee7c6b60bf23cfff679a20f34e808eb6`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M129.020 | `LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue_mul_inv` | 179–182 | `normIntegerUnitsValue_mul_invStatement` |
| M129.021 | `LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue_inv_mul` | 192–195 | `normIntegerUnitsValue_inv_mulStatement` |

## Complete propositions

### `normIntegerUnitsValue_mul_invStatement`

```lean
∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
[ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ),
    normIntegerUnitsValue (K := K) (L := L) x *
      normIntegerUnitsValue (K := K) (L := L) x⁻¹ = 1
```

### `normIntegerUnitsValue_inv_mulStatement`

```lean
∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
[ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ),
    normIntegerUnitsValue (K := K) (L := L) x⁻¹ *
      normIntegerUnitsValue (K := K) (L := L) x = 1
```


## Adaptation and reuse

Worker 202 extracted the source theorem types, prefixed the namespace with
`Langlands.NYLL`, suffixed the names with `Statement`, and moved the complete
source telescopes into their proposition bodies. The mathematical formulas,
binder kinds and order are unchanged. The original proofs and theorem attributes
(including `simp` where present) are omitted. Explicit universe parameters fix
the original order. No instance is introduced.

The imports are exactly:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U019.Definitions`

The earlier source `UnitNorm` section supplies the two implicit fields and
three instances written before the explicit declaration binders here.
The published norm value has the same underlying norm and uses a Mathlib
integrality proof for membership. The statement does not depend on that proof
term. The published unit norm already inlines the inverse proofs; these
propositions export their exact source targets separately.

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
