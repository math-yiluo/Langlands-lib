# Descent of the additive norm estimate through the tame compositum

Module `FontaineWintenberger.FieldOfNorms.Estimates.Tame`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, with residue characteristic `p`, and let `Ω/K` be a finite Galois extension with a compatible ultrametric norm. For a subgroup `H` of `Gal(Ω/K)` with fixed field `F`, not assumed normal over `K`, the file proves the additive congruence of the integral norm of `F/K` when `F/K` is totally ramified of `p`-power degree.

## Results

- `mem_maximalIdeal_pow_of_algebraMap_mem_ceil`: let `R → S` be a local injective map of discrete valuation rings with ramification index `e`, and `b` a real number. If the image of `x` lies in the power `⌈e · b⌉` of the maximal ideal of `S`, then `x` lies in the power `⌈b⌉` of the maximal ideal of `R`. The element `x = 0` is allowed.
- `exists_intNorm_add_congruence_of_totallyRamified_fixedField`: suppose the ramification index of `F/K` equals `[F : K]`, that `[F : K] = p ^ n`, and that `[F : K] > 1`. Then there is a real `b ≥ 0` with `apfRamificationBound K F = b` such that, for all `x`, `y` in `spectralIntegerRing K F`, the element `N(x + y) − N(x) − N(y)`, with `N = Algebra.intNorm 𝒪[K] _`, lies in the power `⌈(p − 1)/p · b⌉` of the maximal ideal of `𝒪[K]`.

## Proof

Let `P` be the first lower ramification group of `Ω/K` and `A` its fixed field, with `e` the ramification index of `A/K`. An earlier result (`exists_apfRamificationBound_wild_compositum_of_totallyRamified`) gives `b` and shows that the ramification bound of `A ⊔ F` over `A` is `e · b`. The extension `A ⊔ F` over `A` lies above wild inertia, so `FiniteIntermediateField.integerNorm_add_congruence_of_wild_field` gives the additive congruence there at precision `⌈(p − 1)/p · e · b⌉`. The norm from `A ⊔ F` to `A` of an element of `F` is the image of its norm from `F` to `K` (`fixedField_wild_norm_baseChange`), so the defect over `K` maps to the defect over `A`, and the first lemma removes the factor `e`.

## To watch for

- Total ramification is expressed with the valuation subring of the restriction to `F` of the spectral valuation of `Ω`, not with `spectralIntegerRing K F`.
- The trivial extension is excluded by `hdegree`.
- `apfRamificationBound` is the library's own invariant, with values in `EReal`; the theorem asserts that it is a finite nonnegative real in this situation.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Estimates/Tame.lean` (SHA-256 of the source file `5e8ea357d046f35d9e1d1717b8907dca35c4cf1bb30b2f7047631839e4f60efc`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
