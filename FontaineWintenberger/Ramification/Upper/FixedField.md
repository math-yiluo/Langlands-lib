# Restriction to a fixed field and Tate's coset identity

Module `FontaineWintenberger.Ramification.Upper.FixedField`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field, `L/K` a Galois extension, `H` a normal subgroup of `L ≃ₐ[K] L`, and `F` the fixed field of `H`. Write `B` for `spectralIntegerRing K L` and `A` for the valuation ring of `F` for the restricted spectral valuation. The file sets up restriction of automorphisms to `F` as a map into the decomposition subgroup `D` of `A`, and proves, for `L/K` finite with perfect residue field, the identity relating the ramification order of a restricted automorphism to the orders of its lifts.

## Main definitions and results

- `restrictNormal_mem_fixedField_decomposition`: the restriction of any `σ` to `F` preserves `A`.
- `fixedFieldDecompositionRestriction K L H`: the restriction homomorphism from `L ≃ₐ[K] L` to `D`.
- `fixedField_decompositionSubgroup_eq_top`: `D` is the whole group of automorphisms of `F` over `K`.
- `fixedFieldDecompositionRestriction_surjective`, `fixedFieldDecompositionRestriction_ker`: the restriction is onto, with kernel `H`.
- `fixedFieldDecompositionQuotientEquiv`: the resulting isomorphism from the quotient by `H` onto `D`.
- `fixedFieldRestrictionFiberEquiv`: the bijection `h ↦ σ * h` from `H` onto the lifts of the restriction of `σ`.
- `fixedFieldDecompositionRestriction_algebraMap`: restriction is compatible with the actions on `A` and `B`.

For `L/K` finite and the residue field of `K` perfect:

- `fixedField_ramificationIdx_mul_order_eq_sum`: the ramification index of `B` over `A` times the order of the restriction of `σ` equals the sum over `h` in `H` of the orders of `σ * h`, in `ℕ∞`.
- `fixedField_card_inertia`: the inertia group of `H` acting on `B` has order that ramification index.
- `fixedField_card_inertia_mul_order_eq_sum`, `fixedField_order_eq_sum_div_ramificationIdx`, `fixedField_order_eq_sum_div_card_inertia`: the same identity with the order of inertia, and as a quotient in `ℝ≥0∞`.
- `fixedField_order_eq_fiber_sum_div_ramificationIdx`, `fixedField_order_eq_fiber_sum_div_card_inertia`: the same for any `τ` in `D`, summing over its lifts.

## Proofs

The identity is `ramificationIdx_mul_order_eq_sum_coset` from the library's file on Tate's identity, applied with generators of `B` and of `A` as algebras over the integers below (`spectralIntegerRing_exists_generator`, `intermediate_spectral_exists_generator`). The order of inertia is `card_lowerRamificationGroup_zero` from the file on inertia.

## Points to watch

- Automorphisms of `F` are handled as elements of the decomposition subgroup of `A`, which is the full group; orders on `F` are `ValuationSubring.ramificationOrder`.
- Orders take values in `ℕ∞`: when the restriction of `σ` is trivial both sides are infinite.
- The statements up to `fixedField_decompositionSubgroup_eq_top`, surjectivity and `fixedFieldDecompositionRestriction_algebraMap` need `L/K` Galois only; the kernel statement, the quotient isomorphism and the bijection with the lifts assume `L/K` finite.
- A perfect residue field is assumed for the identity; the residue field need not be finite.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/FixedField.lean` (SHA-256 of the source file `82575e6c1e4cd8f1047497e8d8f85134eaf8567ae73d0531aea4055375d3eaba`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
