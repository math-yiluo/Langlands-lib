# Unbounded ramification and the residue prime

Module `FontaineWintenberger.APF.Tower.PrimeValuation`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

In an infinite APF extension `L/K`, ramification indices of finite subextensions are unbounded, so the residue characteristic `p` lies in high powers of the maximal ideals of large finite layers.

- `FiniteIntermediateField.exists_tail_finrank_ge`: for an infinite algebraic extension `L/K` of fields, a finite intermediate field `D` and `n`, there is a finite `T ≥ D` with `[E : D] ≥ n` for every finite `E ≥ T`.

For `IsPerfectResidueLocalField K`, `L/K` separable, APF and infinite:

- `IsAPF.exists_finiteIntermediateField_ramificationIdx_unbounded`: there is a finite `W` such that for every finite `D ≥ W` and every `n` the ramification index of `E` over `D` is at least `n` for all finite `E` above some `T ≥ D`.
- `IsAPF.exists_finiteIntermediateField_natCast_mem_maximalIdeal_pow`: for every `n` there is a finite `T` with `p ∈ 𝔪_E ^ n` in `spectralIntegerRing K E` for all finite `E ≥ T`.

On the wild tail degrees equal ramification indices. Infiniteness is an instance `Fact (¬ Module.Finite K L)`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/PrimeValuation.lean` (SHA-256 of the source file `2e3de363cfb813d952f2f57e1a30e0cc4f0e7750d26d9e9c66c0bbe2325a469b`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
