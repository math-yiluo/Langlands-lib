# NYLL M122-integer-valued-norm-data: data

Two exact source structures: an integer-valued multiplicative valuation on an arbitrary group, and a norm-like group homomorphism between two such valued groups with a natural-number scaling coefficient and its valuation formula. The `residueDegree` field is proof-attached data, not an independently asserted field-extension invariant. Both group universes are arbitrary and independent.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Norm/Basic.lean`.
The original file SHA-256 is `e5122c423bfc8d9b3c60683ceab0e1a6ce01df8c2bae954e674118c665588c31`.
The readable original is retained under registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Norm/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source declaration lines | Adapted name |
| --- | --- | --- | --- |
| M122.001 | `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation` | 27–33 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation` |
| M122.119 | `LocalFieldTheory.DiscreteValuationField.ValuedNorm` | 1059–1068 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedNorm` |

## Complete data and context

The Lean module retains the following complete context and data. Only the
namespace prefix changes in this display.

```lean
universe u v

/-- A multiplicative group valuation with values in additive integers. -/
structure MultiplicativeIntegerValuation (G : Type u) [Group G] where
  /-- The integer valuation of a group element. -/
  val : G → ℤ
  /-- The identity has valuation zero. -/
  map_one : val 1 = 0
  /-- Valuation turns multiplication into integer addition. -/
  map_mul : ∀ x y : G, val (x * y) = val x + val y

/-- A norm-like homomorphism compatible with integer-valued valuations.

`residueDegree` is proof-attached data: it is the multiplier in
`valuation_formula`, not an independent field-extension invariant.  In the
usual discrete-valued application the source has a uniformizer, and evaluating
`valuation_formula` at that uniformizer uniquely determines this coefficient.
The generic group-level abstraction does not require a uniformizer, so it keeps
the coefficient together with the formula that certifies it. -/
structure ValuedNorm {G : Type u} {H : Type v} [Group G] [Group H]
    (vG : MultiplicativeIntegerValuation G)
    (vH : MultiplicativeIntegerValuation H) where
  /-- The multiplicative norm homomorphism. -/
  toHom : H →* G
  /-- The nonnegative scaling factor in the valuation formula. -/
  residueDegree : ℕ
  /-- Applying the norm scales valuation by the residue-degree factor. -/
  valuation_formula :
    ∀ x : H, vG.val (toHom x) = (residueDegree : ℤ) * vH.val x
```

## Adaptation and reuse

Worker 202 prefixed the source namespace with `Langlands.NYLL`, retained the
original declaration names, and reduced the import closure to:

- `Mathlib.Algebra.Group.Hom.Defs`
- `Mathlib.Data.Int.Basic`

Both structure headers, all field names and types, field order, and all original structure docstrings are unchanged. The first carrier binder is explicit in `MultiplicativeIntegerValuation`; both carrier binders in `ValuedNorm` are implicit, followed by the two group instances and the two explicit valuations. The source's two NYLL imports supply unrelated unit and subgroup lemmas; neither is needed for these standalone structures. No helper from another source module has been substituted.

The Library and Mathlib were searched for these exact data declarations before
authoring. Related canonical Mathlib structures are reused directly through the
listed imports. This module introduces no global instance and copies no other
worker's draft.

## Attribution and scope

The original copyright and author header is retained verbatim. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain in the Library, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public partition reports no patch10 modification for this module.
This supporting data asserts no host reciprocity, Tate, cup-product, transfer
or class-formation result.
