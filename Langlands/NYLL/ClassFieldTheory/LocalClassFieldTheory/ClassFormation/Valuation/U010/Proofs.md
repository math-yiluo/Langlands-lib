# NYLL M140.010: valuation one versus valuation zero on field units

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zeroStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero`.
The theorem's type is the target applied to all its parameters: a field `L`
in universe `u` with a valuative relation, a topology and the
`IsNonarchimedeanLocalField L` instance, and a field unit `x : Lˣ`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements`.
The published statement and its imported definitions remain unchanged.

The statement is

```lean
valuationUnitsMulHom L x = 1 ↔ valuationMap L (Additive.ofMul x) = 0
```

that is, the multiplicative normalized valuation
`valuationUnitsMulHom L : Lˣ →* Multiplicative ℤ` takes the value `1` at `x`
exactly when the additive normalized valuation
`valuationMap L : Additive Lˣ →+ ℤ` takes the value `0` at `x`.

## Implemented proof

```lean
  unfold valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zeroStatement
  change valuationUnitsMulHom L x = 1 ↔
    Multiplicative.toAdd (valuationUnitsMulHom L x) = 0
  constructor
  · intro hx
    exact congrArg Multiplicative.toAdd hx
  · intro hx
    apply Multiplicative.toAdd.injective
    exact hx
```

The target definition is unfolded. The published `valuationMap L` is
`MonoidHom.toAdditive (valuationUnitsMulHom L)`, so
`valuationMap L (Additive.ofMul x)` is definitionally
`Multiplicative.toAdd (valuationUnitsMulHom L x)`; `change` states the goal in
that form. The forward direction applies `Multiplicative.toAdd` to
`valuationUnitsMulHom L x = 1`, since `Multiplicative.toAdd 1` is `0` by
definition. The reverse direction uses injectivity of the equivalence
`Multiplicative.toAdd`.

The proof uses only the published definitions reached through the statement
import and Mathlib's `Multiplicative.toAdd`. It invokes no NYLL theorem.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`,
lines 206–220 (docstring at lines 206–207, theorem at lines 208–220). The
file's SHA-256 is
`478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`.
The source proof (lines 213–220) is the `change`/`constructor` proof above.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero` | `Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import; the result is expressed as the published target proposition applied
to all its parameters, so the proof first unfolds that definition and then
runs the source proof unchanged. The source `noncomputable section` and all
other source declarations are omitted.

The retained original snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The original copyright, Apache-2.0 license statement and author header are
preserved in the Lean file, followed by the modification record. The
inherited `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain
unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This support lemma proves M140.010 only. It proves no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `312acf7a-3df6-4bad-b4d6-dec474e80ab4` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
