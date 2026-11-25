# Herbrand continuity of the norm without normality

Module `FontaineWintenberger.FieldOfNorms.Estimates.Nonnormal`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a local field in the library's sense `IsPerfectResidueLocalField` (complete, discretely valued, perfect residue field). The file proves that the integral norm of a finite separable, totally ramified extension of `p`-power degree is continuous with modulus the Herbrand function `apfPhi`, with no assumption that the extension is normal.

## Main results

- `intNorm_sub_congruence_of_totallyRamified`: let `L/K` be finite separable, `p` the residue characteristic, the ramification index equal to `[L : K]`, and `[L : K] = p ^ n`. If `x − y` lies in the `r`-th power of the maximal ideal of `spectralIntegerRing K L`, then `Algebra.intNorm x − Algebra.intNorm y` lies in the power `⌈apfPhi K L r⌉` of the maximal ideal of `𝒪[K]`. The case `n = 0` (trivial extension) is included.
- `intNorm_sub_congruence_of_totallyRamified_intermediateField`: the same for an intermediate field `M` of a finite Galois extension `Ω/K`; `M` need not be normal.
- `intNorm_sub_congruence_of_totallyRamified_fixedField`: the same for the fixed field of a subgroup `H` of `Gal(Ω/K)`.
- `spectralIntegerInclusion_sub_mem_pow_ramificationIdx`: for intermediate fields `F ≤ M` of `Ω/K`, the inclusion of integer rings sends a congruence modulo the `r`-th power to a congruence modulo the power `e(M/F) · r`.
- `spectralIntegerInclusion_sub_mem_wild_compositum_pow`: for `F` whose fixing subgroup together with wild inertia `P` generates the Galois group, the inclusion of `F` in `A ⊔ F` multiplies precision by `e(A/K)`, where `A` is the fixed field of `P` (the first lower ramification group).

## Proof

For the fixed field `F` of `H`, the hypotheses give that the fixing subgroup of `F` and `P` together generate the Galois group (`fixedField_sup_wild_eq_top`). One passes to the compositum `A ⊔ F` over `A`, which lies above wild inertia, and applies `FiniteIntermediateField.integerNorm_sub_congruence_of_wild_field` from the file on norm continuity. Tame base change multiplies both the input precision and the Herbrand modulus by `e(A/K)` (`wild_compositum_apfPhi_scaling`), the norm commutes with base change (`fixedField_wild_norm_baseChange`), and a ceiling descent lemma returns to `𝒪[K]`. The intermediate-field form follows by the Galois correspondence, and the general form by embedding `L` in the normal closure inside a separable closure and transporting along the isomorphism onto the image.

## To watch for

- Total ramification is stated as equality of the ramification index with the degree, and the degree must be a power of the residue characteristic `p`; tamely ramified extensions are not covered here.
- In the fixed-field form the ramification index is that of the valuation subring obtained by restricting the spectral valuation of `Ω`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Nonnormal.lean` (SHA-256 of the source file `b8b96f5944bd869137ae4e7cb52d4dabf32cdf3ae72a20ecf79f5c3114e4711a`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
