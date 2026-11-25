# Integral preimages of local norms at finite places

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FiniteIntegralNormPreimage`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields and v a finite place of K. Suppose x ∈ K_vˣ is an integral unit and is the determinant norm of some unit of K_v ⊗_K L. This file shows that the preimage can then be chosen integral, together with its inverse, in every factor of the decomposition of K_v ⊗_K L into the completions of L above v. This is the local input needed to assemble local norm preimages into a relative idele.

## Main results

- `exists_localTensorDecompositionIntegralUnit_localTensorNorm_eq`: if x lies in the range of `localTensorNorm` at v and in the integral units of K_v, there is z ∈ (K_v ⊗_K L)ˣ with norm x that satisfies `RelativeLocalTensorDecompositionIntegralUnitAt` (integral in every factor of the decomposition).
- `v_eq_zero_of_normUnits_eq_integerUnitsToFieldUnits`: let E/F be a finite Galois extension of nonarchimedean local fields, with the valuation of E extending that of F and 𝒪_E the integral closure of 𝒪_F. If the norm of y ∈ Eˣ is an integral unit of F, then y has valuation 0. This uses the formula v_F(N y) = f · v_E(y).
- `exists_finitePlaceCompletionIntegerUnit_of_unitsEquiv_eq`: an integral unit of Mathlib's adic completion K_v comes from an integral unit of the completion of K for the v-adic absolute value.
- `exists_absoluteValueCompletionIntegerUnit_of_localizedCompletion_norm_bounds`: a unit y of the local field L_w with ‖y‖ ≤ 1 and ‖y⁻¹‖ ≤ 1 gives an integral unit of the completion of L at w.
- `singleRelativeLocalTensorDecompositionIntegralUnit`: the unit of K_v ⊗_K L whose component at one extension w is a given integral unit and whose other components are 1. Three companion lemmas give its components, its integrality, and its norm, which is the norm of the w-component (`localTensorDetNorm_singleRelativeLocalTensorDecompositionIntegralUnit_eq`).

## Proof

The imported `finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup` says that the range of the tensor norm is the norm group of the single chosen completion L_w. So x = N(y) for some y ∈ L_wˣ. Since x is an integral unit, y has valuation 0 and is an integral unit of L_w. The required z puts y at w and 1 at every other factor.

## Points to watch

- The main theorem assumes L/K Galois. Several helper lemmas drop that hypothesis.
- The integrality obtained is integrality in each factor of the local decomposition (`RelativeLocalTensorDecompositionIntegralUnitAt`). It is not integrality with respect to a basis of L over K.
- The proof moves between three models of the local fields: Mathlib's adic completion, the completion for an absolute value, and the library's `LocalizedCompletion`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Relative/FiniteIntegralNormPreimage.lean`: the Lean file is the source byte for byte (SHA-256 `cea7efac82edc41b1009f3ca02a2222d3e04be1750cc1b506ca10339fe9697eb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
