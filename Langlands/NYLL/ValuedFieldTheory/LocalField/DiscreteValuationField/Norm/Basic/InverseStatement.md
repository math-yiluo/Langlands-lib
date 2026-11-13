# NYLL M122-valuation-inverse: source statement targets

This module defines 1 proposition targets in
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation`. Each target is a closed `def : Prop`;
its source parameters are universally quantified inside the proposition in
their original order and with their original explicit, implicit and instance
binder kinds. Universe parameters `u` are arbitrary and retain the source
order. This file supplies statements only; their proofs require separate tasks.

The target is the original inverse formula for the actual `val` field
of an arbitrary `MultiplicativeIntegerValuation`. The source section
context at line 37 is retained, including its explicit valuation
argument, before the explicit group element. There are no field,
surjectivity or discreteness assumptions.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Norm/Basic.lean`.
The original file SHA-256 is `e5122c423bfc8d9b3c60683ceab0e1a6ce01df8c2bae954e674118c665588c31`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Norm/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The table gives the source declaration and the lines containing its complete
type (including its proof delimiter); the adapted name is relative to the
prefixed namespace above.

| Unit | Original name | Source type lines | Adapted target |
| --- | --- | --- | --- |
| M122.007 | `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.val_inv` | 77–78 | `val_invStatement` |

## Complete propositions

### `val_invStatement`

```lean
∀ {G : Type u} [Group G] (V : MultiplicativeIntegerValuation G)
(x : G),
    V.val x⁻¹ = -V.val x
```


## Adaptation and reuse

Worker 202 extracted the source theorem types, prefixed the namespace with
`Langlands.NYLL`, suffixed the names with `Statement`, and moved the complete
source telescopes into their proposition bodies. The mathematical formulas,
binder kinds and order are unchanged. The original proofs and theorem attributes
(including `simp` where present) are omitted. Explicit universe parameters fix
the original order. No instance is introduced.

The imports are exactly:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic.Definitions`

The companion `Definitions` pair contains the exact source structure.
The target does not depend on the source's auxiliary `valuationHom`
or the lemmas preceding it. Its source `simp` attribute and proof
are omitted; proving this target is a separate task.

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
