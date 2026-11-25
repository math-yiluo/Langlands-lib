# Discretely valued fields: the basic structure

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file introduces the library's notion of a discretely valued field: a field `K` with a chosen valuation whose value group is a linearly ordered commutative group with zero and which is discrete of rank one. It develops the valuation ring `O`, its maximal ideal `𝔪`, the residue field, uniformizers, and the graded pieces `𝔪ⁿ/𝔪ⁿ⁺¹`.

## Main definitions

- `DVF K`: a structure bundling a value group `ValueGroup`, a Mathlib `Valuation` on `K` with values in it, and an instance that it is `IsRankOneDiscrete`.
- For `F : DVF K`: `valuationSubring` (with ring, local ring and domain instances), `maximalIdeal`, `residueField` (with its field structure), `residueMap`.
- `MaximalIdealPowSuccQuot F n`: the quotient `𝔪ⁿ/𝔪ⁿ⁺¹` as an `O`-module, with its quotient map `maximalIdealPowSuccQuotMk`, induction principles and lifting constructions.
- `maximalIdealPowSuccQuotMulUniformizerPowMap`: the map `O → 𝔪ⁿ/𝔪ⁿ⁺¹`, `r ↦ r ϖⁿ`.
- `residueLinearEquivMaximalIdealPowSuccQuotOfUniformizer` (and its additive form): the `O`-linear isomorphism `O/𝔪 ≃ 𝔪ⁿ/𝔪ⁿ⁺¹` given by multiplication by `ϖⁿ`.

An instance `ValuationSubring.charP` gives a valuation subring the characteristic of its field.

## Main results

- The valuation ring is a discrete valuation ring with fraction field `K`, integrally closed and noetherian.
- Membership: `x ∈ O ↔ v x ≤ 1`, `x ∈ 𝔪 ↔ v x < 1`; a residue is zero if and only if the element lies in `𝔪`, and nonzero if and only if it is a unit; the residue map is surjective.
- Uniformizers: one exists (`exists_uniformizer`); a uniformizer `ϖ` generates `𝔪`, and `ϖⁿ` generates `𝔪ⁿ`, so `x ∈ 𝔪ⁿ ↔ ϖⁿ ∣ x`; `ϖⁿ ∉ 𝔪ⁿ⁺¹`; `𝔪 ≠ ⊥`.
- `nonzero_ideal_eq_maximalIdeal_pow`: every nonzero ideal of `O` is a power of `𝔪`.
- `isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq`: an element of `𝔪 ∖ 𝔪²` is a uniformizer; multiplying a uniformizer by a unit keeps it outside `𝔪²`.
- The map `r ↦ r ϖⁿ` into `𝔪ⁿ/𝔪ⁿ⁺¹` is surjective with kernel `𝔪`, which gives the isomorphism with the residue field; its value on a residue class is computed by a simp lemma.

## Points to watch

`DVF` is the library's own structure, not a Mathlib class: the valuation is data, and the value group is a field of the structure, living in a separate universe `v`. Uniformizers are in the sense of Mathlib's `Valuation.IsUniformizer`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `f1631ec8fd451ed82a6ba58b43149683380589d0db3ff422d73dcef68567e798`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
