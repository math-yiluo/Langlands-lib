# NYLL M128.008–M128.009: valuation of natural and integral powers (statement targets)

This module defines two proposition targets in
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. They concern the
normalized valuation `v K : Additive Kˣ → Int` of a nonarchimedean local field.
They say that `v` turns powers of a field unit into integer multiples of its
valuation:

- `v_powStatement` (source unit M128.008): for a unit `x` and `n : Nat`,
  `v K (x ^ n) = n * v K x`;
- `v_zpowStatement` (source unit M128.009): for a unit `x` and `n : Int`,
  `v K (x ^ n) = n * v K x`.

Each target is a closed `def … : Prop`. The complete source telescope is
universally quantified inside the proposition, in its original order and with
its original binder kinds. The explicit universe parameter `u` is the source's
`universe u`. Defining these propositions does not prove them; their proofs are
separate tasks.

## Complete propositions

### `v_powStatement`

```lean
def v_powStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat),
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x)
```

Here `x ^ n` is the monoid power in the unit group `Kˣ`, `Additive.ofMul`
views a unit as an element of `Additive Kˣ` (the domain of `v`), and the
right-hand side is the product in `Int` of the cast `(n : Int)` with the
valuation of `x`.

### `v_zpowStatement`

```lean
def v_zpowStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int),
    v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x)
```

Here `x ^ n` is the integer power in the group `Kˣ` (so `x ^ (-1) = x⁻¹`).

## Parameters and meaning

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K` | explicit, `Type u` | The local field |
| `[Field K]` | instance-implicit | Field structure |
| `[ValuativeRel K]` | instance-implicit | Mathlib valuative relation, with canonical valuation `ValuativeRel.valuation K` |
| `[TopologicalSpace K]` | instance-implicit | Topology of `K` |
| `[IsNonarchimedeanLocalField K]` | instance-implicit | Mathlib's nonarchimedean local-field certificate (`Mathlib/NumberTheory/LocalField/Basic.lean`) |
| `x` | explicit, `Kˣ` | A field unit |
| `n` | explicit, `Nat` (M128.008) or `Int` (M128.009) | The exponent |

`v` is the published Library definition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` (source unit
M128.001, module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`).
It sends a unit to the exponent of its value under Mathlib's
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K`, which identifies the
value group with `WithZero (Multiplicative Int)`. The source shows separately
that `v K` is surjective (M128.003) and that some unit has valuation `1`
(`v_uniformiser`, M128.015). The two targets here do not depend on this
normalization, since both of their sides are linear in `v`.

So the targets are the statements that `v`, viewed on `Kˣ`, is a group
homomorphism with respect to powers: the valuation of `xⁿ` is `n` times the
valuation of `x`, first for natural and then for integer exponents. These are
the source's `v_pow` and `v_zpow`.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
SHA-256 `c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.
The readable original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Unit | Original name | Docstring | Statement lines | Proof lines | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M128.008 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_pow` | 112 | 113–115 | 115–122 | `v_powStatement` |
| M128.009 | `LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow` | 124–125 | 126–128 | 128–136 | `v_zpowStatement` |

The source file opens `namespace LocalFieldTheory` (line 15),
`noncomputable section` (line 17), declares `universe u` (line 19), opens
`namespace IsNonarchimedeanLocalField` (line 21) and `open scoped ValuativeRel WithZero`
(line 23). No `variable` is in scope, so each theorem's binders are its whole
telescope. The source statements are:

```lean
theorem v_pow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat) :
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x) := by

theorem v_zpow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int) :
    v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x) := by
```

The binders and the conclusions are copied verbatim into the targets. (The
source docstring of `v_zpow` repeats its sentence twice; the target docstring
states it once.)

## Adaptation and reuse

Worker 85 extracted the two source theorem types, prefixed the namespace with
`Langlands.NYLL`, suffixed the names with `Statement`, and moved each complete
source telescope into its proposition body. The mathematical formulas, binder
kinds and order are unchanged. The proofs are omitted. This follows the format
of the published sibling module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements`
(source units M128.002–M128.006 and M128.019), which these targets do not import
or modify.

The only import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`,
which provides `v` and, through it, the source's Mathlib import
`Mathlib.NumberTheory.LocalField.Basic`. No instance is introduced. The scoped
`ValuativeRel` and `WithZero` notations are opened as in the source; the target
bodies do not use them.

As a consistency check (not part of this module), the source proofs of
`v_pow` and `v_zpow` were replayed in a private draft against these targets
together with the published `v_mulStatement`, `v_oneStatement` and
`v_invStatement` as hypotheses; both compiled unchanged. This confirms that the
targets elaborate to the source's equations.

The published Library and Mathlib were searched for these exact targets before
authoring; none declares them. No other worker's draft is copied.

## Consumers

Source unit M162.017 (`v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable`)
uses `v_pow` in its proof, and M162.019
(`v_normUnits_eq_residue_finrank_mul_of_isSeparable`, target
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement`)
uses `v_zpow` in its proof. Both lie in the M258 NormResidue closure of Task 5264.

## Attribution

The original copyright and author header is retained verbatim, followed by a
modification record. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain in the Library, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This support unit asserts no host reciprocity, Tate, cup-product, transfer or
class-formation result.
