# Valuation-ring units from field units of valuation zero: statement targets (M134.028, M134.039, M134.040)

This module defines three proposition targets in
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. Each target is a
closed `def … : Prop` with the single universe parameter `u`. The source
parameters are universally quantified inside the proposition, in their
original order and with their original explicit and instance binder kinds.
This file supplies statements only; their proofs are left to a separate
proof task.

Throughout, `K : Type u` is a nonarchimedean local field (a field with
`[ValuativeRel K]`, `[TopologicalSpace K]` and Mathlib's
`[IsNonarchimedeanLocalField K]`), `𝒪[K]` is its valuation ring, and
`v(x) = valuationMap K (Additive.ofMul x)` for a field unit `x : Kˣ`.

## Sign convention

NYLL's `valuationMap` is the **negative** of the usual normalized discrete
order `ord`, for which a prime element `π` of `𝒪[K]` has `ord(π) = 1`; so
`v(x) = -ord(x)`. The map is built from Mathlib's order-preserving
isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` onto
`WithZero (Multiplicative ℤ)`, so elements of valuation less than one get
negative integers. The source proves that a prime element of `𝒪[K]` has
`v = -1` and its inverse has `v = 1` (`v_integerRingIrreducibleFieldUnit`
and `v_integerRingIrreducibleFieldUnit_inv`, original `IdealQuotients.lean`,
lines 210–244), and `valuationMap K x = v K x` holds by `rfl` (original
`ValuationExactSequence.lean`, lines 30–54). The published audit
`notes/reuse/nyll-finite-local-reciprocity-audit.md` (section 2.3) records
the same convention.

Consequently the hypothesis `hϖ : valuationMap K (Additive.ofMul ϖ) = 1` in
M134.039 and M134.040 makes `ϖ` an **inverse** uniformizer: `ϖ⁻¹` is a prime
element of `𝒪[K]`. The source names and the decomposition
`x = u · ϖ ^ v(x)` are kept unchanged; in usual terms it reads
`x = u · (ϖ⁻¹) ^ ord(x)`. The targets neither choose nor redefine a
uniformizer, and the source sign is unchanged.

## The targets

### `integerUnitOfValuationMapZero_specStatement` (M134.028)

```lean
def integerUnitOfValuationMapZero_specStatement.{u} : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0),
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x
```

For every field unit `x` with `v(x) = 0`, the valuation-ring unit
`integerUnitOfValuationMapZero K x hx` maps back to `x` under the inclusion
`integerUnitsToFieldUnits K : 𝒪[K]ˣ →* Kˣ`. The condition `v(x) = 0` does not
depend on the sign convention.

### `integerUnitsToFieldUnits_uniformizerUnitFactorStatement` (M134.039)

```lean
def integerUnitsToFieldUnits_uniformizerUnitFactorStatement.{u} : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ),
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x)
```

For every field unit `ϖ` with `v(ϖ) = 1` (an inverse uniformizer) and every
field unit `x`, the field unit underlying `uniformizerUnitFactor K ϖ hϖ x` is
`x / ϖ ^ v(x)`, with the integer power `zpow` in the group `Kˣ`.

### `uniformizerUnitFactor_mul_uniformizer_zpowStatement` (M134.040)

```lean
def uniformizerUnitFactor_mul_uniformizer_zpowStatement.{u} : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ),
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) *
        ϖ ^ valuationMap K (Additive.ofMul x) = x
```

Under the same hypotheses, `u · ϖ ^ v(x) = x` in `Kˣ`, where `u` is the field
unit underlying `uniformizerUnitFactor K ϖ hϖ x`. With `π = ϖ⁻¹` a prime
element of `𝒪[K]` this is the usual decomposition `x = u · π ^ ord(x)`.

## The objects involved

All names below are published in the Library or in Mathlib.

- `valuationMap K : Additive Kˣ →+ ℤ`
  (`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`,
  source M134.002, module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`)
  is NYLL's integer valuation on field units, with the sign convention above.
- `integerUnitsToFieldUnits K : 𝒪[K]ˣ →* Kˣ` (source M128.016, module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`)
  is `Units.map` of the inclusion `𝒪[K] → K`.
- `integerUnitOfValuationMapZero K x hx : 𝒪[K]ˣ` (source M134.027) is the
  unit of `𝒪[K]` with underlying element `x` and inverse `x⁻¹`, for a field
  unit `x` with `v(x) = 0`.
- `uniformizerUnitFactor K ϖ hϖ x : 𝒪[K]ˣ` (source M134.038) is
  `integerUnitOfValuationMapZero K (x / ϖ ^ v(x)) _`.

The last two are defined in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U027.Definitions`.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean),
SHA-256 `8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`.
Lines 20–28 open `namespace LocalFieldTheory`, `noncomputable section`,
`universe u`, `namespace IsNonarchimedeanLocalField` and
`open scoped ValuativeRel WithZero`; the file has no section variables, so
each theorem takes all its parameters as its own binders.

| Unit | Original theorem | Source lines (docstring to proof) | Adapted target |
| --- | --- | --- | --- |
| M134.028 | `LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero_spec` (`@[simp]`) | 272–280 | `integerUnitOfValuationMapZero_specStatement` |
| M134.039 | `LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_uniformizerUnitFactor` (`@[simp]`) | 435–445 | `integerUnitsToFieldUnits_uniformizerUnitFactorStatement` |
| M134.040 | `LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor_mul_uniformizer_zpow` | 447–454 | `uniformizerUnitFactor_mul_uniformizer_zpowStatement` |

Each target body is the source theorem's binder telescope followed by its
conclusion, character for character, with `(K : Type u)` and the instance
binders first. Rows M134.028, M134.039 and M134.040 of the published
partition
[`notes/reuse/nyll-public-port/m121-m144.md`](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md)
assign the source theorem names, in the prefixed namespace, to the adapted
theorems; those names are reserved for the proofs. As in the published
`ValuationExactSequence/KernelStatements` targets, each statement target
adds the suffix `Statement` to that name.
The Library's `notes/errata/` has no NYLL entry. No declaration of these
names, and no equivalent target, exists in the current Library or Mathlib.

The source proofs are short: M134.028 is `ext; rfl`; M134.039 applies
M134.028 to `x / ϖ ^ v(x)` with `uniformizerUnitFactorValuationZero`; and
M134.040 rewrites with M134.039 and finishes with
`simp [div_eq_mul_inv, mul_assoc]`. A private probe, not part of this
module, replays these proofs against the three closed targets with zero
errors; that development check is not independent acceptance.

## Adaptation and modification record

Worker 85 extracted these three theorem types on 14 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalFieldTheory` becomes `Langlands.NYLL.LocalFieldTheory`,
  and each name gets the suffix `Statement`;
- each theorem becomes a closed Prop-valued definition whose body
  universally quantifies the source telescope; the universe `u` is an
  explicit parameter `.{u}` instead of a `universe` command;
- the proofs and the `@[simp]` attributes of M134.028 and M134.039 are
  omitted, and new docstrings describe the targets (they also note the
  inverse-uniformizer reading of `hϖ`);
- the module docstring gains a sentence on the sign convention;
- the imports are replaced as described below.

The binder kinds, binder order, types and conclusions are unchanged. No
theorem, instance, notation or alias is introduced. Every other source
declaration is omitted.

The direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`,
  defining `integerUnitsToFieldUnits`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U027.Definitions`,
  defining `integerUnitOfValuationMapZero` and `uniformizerUnitFactor`, and
  bringing in `valuationMap` and Mathlib's local-field classes.

They replace the source's NYLL imports (`Valuation` and `IdealQuotients`) and
its Mathlib imports `Mathlib.Algebra.Group.Hom.Basic` and
`Mathlib.RingTheory.Valuation.Discrete.Basic`.

## Checks

The module compiled with zero errors and zero warnings in approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports each of the
three declarations as a definition with the single level parameter `u`,
whose type is `Prop`, using only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. Worker 85
adapted these units directly from the pinned original; no other project
worker supplied code.
