# Norm continuity at Herbrand precision above wild inertia

Module `FontaineWintenberger.FieldOfNorms.Estimates.NormContinuity`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `Ω/K` a separable extension carrying a compatible ultrametric norm. For finite intermediate fields `E ≤ F`, the file shows that the integral norm `integerNorm E F` is continuous with modulus the Herbrand function `apfPhi` of `F/E`: first for cyclic steps of prime degree, then, by composition, for every step above the fixed field of wild inertia in a finite Galois `Ω/K`.

## Main results

- `apfPhi_finiteBase_comp_of_normedAlgebra`: for a tower `K ⊆ M ⊆ N` of finite separable extensions, `apfPhi K M (apfPhi M N r) = apfPhi K N r`.
- `FiniteIntermediateField.apfPhi_tower`: the same for three finite intermediate fields `E ≤ F ≤ G` of `Ω/K`, with the relative algebra structures given by the inclusions.
- `FiniteIntermediateField.integerNorm_prime_sub_congruence`: let `F/E` be Galois of prime degree `p` and totally ramified (ramification index equal to the degree). If `x − y` lies in the `r`-th power of the maximal ideal of the integers of `F`, then `integerNorm x − integerNorm y` lies in the power `⌈apfPhi E F r⌉` of the maximal ideal of the integers of `E`.
- `FiniteIntermediateField.integerNorm_sub_congruence_tower`: continuity statements compose. If the norm of `F ≤ G` sends precision `r` to `s` and that of `E ≤ F` sends `s` to `t`, the norm of `E ≤ G` sends `r` to `t`.
- `FiniteIntermediateField.integerNorm_sub_congruence_of_wild_field`: let `Ω/K` be finite Galois with residue characteristic `p`, and let `P` be the first lower ramification group. For finite intermediate fields `E ≤ F` with `E` containing the fixed field of `P`, the norm `integerNorm E F` sends precision `r` to precision `⌈apfPhi E F r⌉`.

## Proofs

The composition of `apfPhi` is obtained by inverting the composition of `apfPsi` (`IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra`). The prime-degree statement transports `spectralIntegerRing_prime_norm_sub_congruence` along the identification of the two descriptions of the integer rings. For the last theorem, the fixing subgroup of `E` is a `p`-group, so `relative_prime_field_chain` gives a chain of cyclic Galois steps of degree `p` from `E` to `F`; each step is totally ramified by `wildField_step_ramificationIdx_eq_finrank`. Induction along the chain composes the prime-degree estimates, using monotonicity and composition of the private helper `finitePhi`.

## To watch for

- `finitePhi`, listed among the main definitions in the file's header, is private; it is `apfPhi` for the inclusion of two finite intermediate fields.
- In the statements the upper field is `IntermediateField.extendScalars hEF`, that is, `F` regarded over `E`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/NormContinuity.lean` (SHA-256 of the source file `c97af5e263d29f796e15976489f6345bdf00b91779fc72d1eb3d07a0492b3342`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
