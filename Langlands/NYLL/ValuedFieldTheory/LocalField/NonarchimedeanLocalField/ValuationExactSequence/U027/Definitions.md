# Valuation-ring units from field units of valuation zero (M134.027, M134.038)

Let `K` be a nonarchimedean local field, `𝒪[K]` its valuation ring and
`valuationMap K : Additive Kˣ →+ ℤ` NYLL's integer valuation on field units.
Write `v(x) = valuationMap K (Additive.ofMul x)`.

**Sign convention.** NYLL's `valuationMap` is the *negative* of the usual
normalized discrete order `ord` (with `ord(π) = 1` for a prime element `π` of
`𝒪[K]`): `v(x) = -ord(x)`. It is built from Mathlib's
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`, an order-preserving
isomorphism onto `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, so elements of
valuation less than one get negative integers. The source proves that a
prime element of `𝒪[K]` has `v = -1` and its inverse has `v = 1`
(`v_integerRingIrreducibleFieldUnit` and
`v_integerRingIrreducibleFieldUnit_inv`, original
`IdealQuotients.lean`, lines 210–244; `valuationMap K x = v K x` by `rfl`,
original `ValuationExactSequence.lean`, lines 30–54). The published audit
`notes/reuse/nyll-finite-local-reciprocity-audit.md` (section 2.3) records
the same convention.

This module defines two maps into the group `𝒪[K]ˣ` of valuation-ring units:

- `integerUnitOfValuationMapZero K x hx` (source M134.027): a field unit `x`
  with `v(x) = 0`, viewed as a unit of `𝒪[K]`. Its underlying element of `K`
  is `x` and that of its inverse is `x⁻¹`. (The condition `v(x) = 0` does not
  depend on the sign convention.)
- `uniformizerUnitFactor K ϖ hϖ x` (source M134.038): for a field unit `ϖ`
  with `v(ϖ) = 1`, the unit factor `u` of the decomposition
  `x = u · ϖ ^ v(x)`. It is `integerUnitOfValuationMapZero` applied to
  `x / ϖ ^ v(x)`, which has `v = 0`. Because of the sign convention, `ϖ` is
  an **inverse** uniformizer: `ϖ⁻¹` is a prime element of `𝒪[K]`. In usual
  terms the decomposition reads `x = u · (ϖ⁻¹) ^ ord(x)`.

Both are definitions in the namespace
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`, with the source
names.

## The Lean definitions

```lean
namespace Langlands.NYLL.LocalFieldTheory
noncomputable section
universe u
namespace IsNonarchimedeanLocalField
open scoped ValuativeRel WithZero

def integerUnitOfValuationMapZero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) : 𝒪[K]ˣ where
  val := ⟨(x : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  inv := ⟨(x⁻¹ : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  val_inv := by
    apply Subtype.ext
    change (x : K) * (x : K)⁻¹ = 1
    exact mul_inv_cancel₀ x.ne_zero
  inv_val := by
    apply Subtype.ext
    change (x : K)⁻¹ * (x : K) = 1
    exact inv_mul_cancel₀ x.ne_zero

noncomputable def uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x : Kˣ) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)
```

## The construction

`integerUnitOfValuationMapZero K x hx` is a structure `Units 𝒪[K]` with four
fields:

- `val` is `x : K` packaged as an element of `𝒪[K]`. The membership proof
  rewrites membership by `valuation_integer_membership` to
  `ValuativeRel.valuation K x ≤ 1`. The published
  `valuation_eq_one_of_valuationMap_eq_zero K hx` gives
  `ValuativeRel.valuation K x = 1`, and `simp` closes the goal.
- `inv` is `x⁻¹ : K` packaged in the same way. Since the valuation is
  multiplicative, the valuation of `x⁻¹` is `1⁻¹ = 1`; `simp` uses this.
- `val_inv` and `inv_val` say that the two elements multiply to `1` in both
  orders. After `Subtype.ext` this is `x * x⁻¹ = 1` and `x⁻¹ * x = 1` in `K`,
  Mathlib's `mul_inv_cancel₀` and `inv_mul_cancel₀` for the nonzero `x`.

So the data of the unit are `x` and `x⁻¹`; the proofs only certify
membership and invertibility. The value does not depend on the proof `hx`.

`uniformizerUnitFactor K ϖ hϖ x` applies `integerUnitOfValuationMapZero` to
the field unit `x / ϖ ^ v(x)`, with the integer power `zpow` of units. The
required valuation-zero proof is the published
`uniformizerUnitFactorValuationZero K ϖ x hϖ`. Its underlying element of `K`
is therefore `x / ϖ ^ v(x)`. The source states this as the theorem
`integerUnitsToFieldUnits_uniformizerUnitFactor` (M134.039), which is not
part of this module.

The hypothesis `hϖ` says that `v(ϖ) = 1`. Under NYLL's sign convention
(see the start of this file) this makes `ϖ` an inverse uniformizer: its
inverse `ϖ⁻¹` lies in `𝒪[K]` and is a prime element there, with usual order
`ord(ϖ⁻¹) = 1`. The source name `uniformizerUnitFactor` and its docstring
are inherited unchanged; they do not mean that `ϖ` itself is a uniformizer
of `𝒪[K]` in the usual sense. The unit `u = x / ϖ ^ v(x)` equals the usual
unit part `x · π ^ (-ord(x))` for the prime element `π = ϖ⁻¹`. The
definition uses `hϖ` only inside the valuation-zero proof.

## The objects involved

All names below are published in the Library or in Mathlib.

- `IsNonarchimedeanLocalField K` is Mathlib's class of nonarchimedean local
  fields, for a field with a valuative relation and a topology.
- `𝒪[K]` is Mathlib's notation, scoped in `ValuativeRel`, for
  `Valuation.integer (ValuativeRel.valuation K)`: the subring of the
  elements of `K` of valuation at most one. `𝒪[K]ˣ` is its group of units.
- `valuationMap K`
  (`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`,
  source M134.002) is NYLL's integer valuation `Additive Kˣ →+ ℤ`, the
  negative of the usual normalized order (see the sign convention above).
- `valuation_integer_membership`
  (source M130.001, module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation.U001.Proofs`)
  proves `valuation_integer_membershipStatement`: for every field `K` with a
  valuative relation and `x : K`, `x ∈ 𝒪[K] ↔ ValuativeRel.valuation K x ≤ 1`.
- `valuation_eq_one_of_valuationMap_eq_zero`
  (source M134.020, module `...ValuationExactSequence.U020.Proofs`) proves
  `valuation_eq_one_of_valuationMap_eq_zeroStatement`: a field unit with
  `v(x) = 0` has `ValuativeRel.valuation K x = 1`.
- `uniformizerUnitFactorValuationZero`
  (source M134.037, module `...ValuationExactSequence.U037.Proofs`) proves
  `uniformizerUnitFactorValuationZeroStatement`: if `v(ϖ) = 1`, then
  `v(x / ϖ ^ v(x)) = 0`.

The three published theorems have closed statement types: each type is a
Prop-valued definition whose body quantifies over the field and its
instances. The source bodies apply them exactly as in the source, to `K`,
`hx` and `K ϖ x hϖ`. Lean unfolds the statement definitions when it applies
or rewrites with these theorems, so the source text elaborates unchanged.

## Source and binders

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean),
SHA-256 `8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`.
The relevant lines are:

- lines 20–28: `namespace LocalFieldTheory`, `noncomputable section`,
  `universe u`, `namespace IsNonarchimedeanLocalField` and
  `open scoped ValuativeRel WithZero`;
- M134.027: the docstring at line 251 and the definition at lines 252–270;
- M134.038: the docstring at line 426 and the definition at lines 427–433.

Both source definitions take all their parameters as their own binders; the
source file has no section variables. The binders, their kinds and their
order are unchanged. The field `K` is in an arbitrary universe `u`, as in
the source, so each definition has the single universe parameter `u`.

## Declaration map

The Library's `notes/errata/` has no NYLL entry. Rows M134.027 and M134.038
of the published partition
[`notes/reuse/nyll-public-port/m121-m144.md`](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md)
assign the adapted names used here. No declaration of either name exists in
the current Library or Mathlib.

| Original declaration | Adapted declaration |
| --- | --- |
| def `LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero` (M134.027) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero` (this module) |
| def `LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor` (M134.038) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor` (this module) |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` (M134.002, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap` (published) |
| theorem `LocalFieldTheory.IsNonarchimedeanLocalField.valuation_integer_membership` (M130.001, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuation_integer_membership` (published) |
| theorem `LocalFieldTheory.IsNonarchimedeanLocalField.valuation_eq_one_of_valuationMap_eq_zero` (M134.020, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuation_eq_one_of_valuationMap_eq_zero` (published) |
| theorem `LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactorValuationZero` (M134.037, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactorValuationZero` (published) |

## Imports and modification record

The direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation.U001.Proofs`,
  proving `valuation_integer_membership`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U020.Proofs`,
  proving `valuation_eq_one_of_valuationMap_eq_zero`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U037.Proofs`,
  proving `uniformizerUnitFactorValuationZero`.

Through them come `valuationMap`, Mathlib's `IsNonarchimedeanLocalField`, the
notation `𝒪[K]` and the unit and group lemmas used in the bodies. These
imports replace the source's NYLL imports (`Valuation` and `IdealQuotients`)
and its Mathlib imports `Mathlib.Algebra.Group.Hom.Basic` and
`Mathlib.RingTheory.Valuation.Discrete.Basic`. Every transitive import lies in
the approved Mathlib environment or the published Library.

Worker 85 extracted these two definitions on 14 November 2026. The Lean
header records the change. The changes are:

- the namespace `LocalFieldTheory` becomes `Langlands.NYLL.LocalFieldTheory`;
  the names are unchanged;
- the imports are replaced as described above.

The binders, types and bodies are unchanged, including the docstrings and the
`noncomputable` modifier of M134.038. In particular the source docstring of
`uniformizerUnitFactor` ("the standard decomposition `x = u * ϖ ^ v(x)`") is
kept verbatim; this file explains above that its `ϖ` is an inverse
uniformizer under NYLL's sign convention. No comment or docstring was
changed. Every other source declaration is
omitted, including the theorems M134.028, M134.039 and M134.040 about these
definitions. No theorem, instance, notation or alias is introduced.

## Checks

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports
`integerUnitOfValuationMapZero` as a definition with the single level
parameter `u`, using only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

A private probe, not part of this module, also compiled with zero errors. In
it, for a field `K : Type`, `rfl` proves that the underlying element of `K`
of `integerUnitOfValuationMapZero K x hx` is `x`, and that of
`uniformizerUnitFactor K ϖ hϖ x` is `x / ϖ ^ v(x)`. These development checks
are not independent acceptance.

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
