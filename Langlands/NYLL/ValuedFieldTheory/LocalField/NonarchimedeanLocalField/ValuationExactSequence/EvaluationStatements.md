# NYLL M134-evaluation-surjectivity: source statement targets

This module defines 2 proposition targets in
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

The actual published additive homomorphism `valuationMap K` has domain
`Additive Kˣ` and codomain `Int`. These targets record its evaluation by
the published `v` and its surjectivity, in the unchanged inverse-standard
source convention.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`.
The original file SHA-256 is `8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M134.004 | `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply` | 51–53 | `valuationMap_applyStatement` |
| M134.005 | `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective` | 57–59 | `valuationMap_surjectiveStatement` |

## Complete propositions

### `valuationMap_applyStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
    valuationMap K x = v K x
```

### `valuationMap_surjectiveStatement`

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    Function.Surjective (valuationMap K)
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
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`

The original imports for ideal quotients and valuation proofs are unnecessary
for these formulas. Both named functions are reused from the Library.

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
