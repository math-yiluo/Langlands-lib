# Tate's divisibility argument for the coset identity

Module `FontaineWintenberger.Ramification.Upper.Tate`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R → A → B` be a tower of commutative rings in which `A` and `B` are generated over `R` by single elements `y` and `x`, and let a finite group `H` act on `B` with invariants `A`. The file proves the identity expressing the ramification order of an automorphism `τ` of `A` as a scaled sum of the orders of the elements of a coset `σH` lifting it.

## Main results

- `generator_sub_dvd_aut_sub`: if `Algebra.adjoin R {y} = ⊤` in `A` and `τ : A ≃ₐ[R] A`, then `τ y - y` divides `τ c - c` for every `c` in `A`.
- `generator_sub_dvd_aeval_map`: for `f` in `A[X]` with `f(x) = 0`, the image of `τ y - y` in `B` divides the value at `x` of `f` with `τ` applied to its coefficients.
- `aeval_map_minpoly_dvd_generator_sub`: if `A` is an integrally closed domain, `B` a torsion-free domain over `A`, and `x` generates `B` over `R` and is integral over `A`, the value at `x` of the `τ`-twisted minimal polynomial of `x` over `A` divides the image of `τ y - y`.
- `associated_generator_sub_aeval_map_minpoly`, `addVal_generator_sub_eq_aeval_map_minpoly`: these two elements are associated, with equal valuation when `B` is a discrete valuation ring.
- `map_minpoly_eq_prod_conjugates`: if `IsGaloisGroup H A B`, with `A` integrally closed, and `x` generates `B` over `A`, the minimal polynomial of `x` over `A` becomes `∏ (X - h • x)` over `B`, the product over `H`.
- `map_minpoly_eq_prod_twisted`, `aeval_map_minpoly_eq_prod_displacements`, `addVal_aeval_map_minpoly_eq_sum`: if `σ : B ≃ₐ[R] B` extends `τ`, the twisted minimal polynomial is `∏ (X - σ (h • x))`, and the valuation of its value at `x` is the sum of the valuations of `σ (h • x) - x`.
- `ramificationIdx_mul_order_eq_sum_coset`: let `A → B` be a local injective map of discrete valuation rings, `G` a group acting on `B` commuting with `R`, `H` a finite subgroup with `IsGaloisGroup H A B`, and `σ` in `G` inducing `τ` on `A`. Then the ramification index of `B` over `A` times `ramificationOrder τ` equals the sum over `h` in `H` of `ramificationOrder (σ * h)`, in `ℕ∞`.

## Proofs

The product formula compares the minimal polynomial with the characteristic polynomial of the action by degrees. The last statement uses `ramificationOrder_eq_generator`: the order of an automorphism is the valuation of its displacement of a generator.

## Points to watch

- Monogenicity of `A` and of `B` over `R` (the hypotheses `hx`, `hy`) is assumed, not proved here.
- The identity holds in `ℕ∞`, including when `τ` is the identity.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/Tate.lean` (SHA-256 of the source file `ae59050c97908cd3f1633213775bcb274498d0c308bbbb448f65e71b3e32be37`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The file did not compile on the Library's Mathlib, which is older than the one the source was written for, and was repaired: Specified the intermediate scalar ring in Algebra.subset_adjoin to avoid a unification timeout in adjoin_singleton_eq_top_over_intermediate.
