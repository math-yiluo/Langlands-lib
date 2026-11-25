# APF extensions under a finite change of base

Module `FontaineWintenberger.APF.BaseChange.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `M` an intermediate field of `SeparableClosure K` that is finite over `K`, with the spectral norm, and `N` a field over `M`, separable over `K`. The file compares the APF data of `N/K` and of `N/M`: the APF subgroups, the predicate `IsAPF`, the index `apfIndex`, and the function `ψ = apfPsi`.

## Setting

The absolute Galois group `G_M` of `M` is mapped into `G_K` by `ρ`, the isomorphism `absoluteGaloisBaseChangeEquiv K M` onto the fixing subgroup of `M` followed by the inclusion. `baseChangedSeparableEmbedding K M i` turns an `M`-embedding `i : N → SeparableClosure M` into a `K`-embedding `N → SeparableClosure K`; its image contains `M` (`le_baseChangedSeparableEmbedding_fieldRange`).

## Results

- `absoluteGaloisBaseChange_range`, `absoluteGaloisBaseChange_range_finiteIndex`: the image of `ρ` is the fixing subgroup of `M`, of finite index.
- `comap_fixingSubgroup_baseChangedEmbedding`: `ρ` pulls the fixing subgroup of the image of `N` back to the fixing subgroup of `i(N)`.
- `comap_absoluteUpper_finiteBase`: for `u ≥ -1`, the preimage of `absoluteUpperRamificationGroup K u` under `ρ` is `absoluteUpperRamificationGroup M (apfPsi K M u)`.
- `comap_apfSubgroup_finiteBase`: for `u ≥ -1`, the preimage of `apfSubgroup K _ u` is `apfSubgroup M _ (apfPsi K M u)`; `comap_apfInertiaSubgroup_finiteBase` is the same for the inertia subgroups, `u ≥ 0`.
- `isAPF_finiteBase_iff`: `IsAPF K N ↔ IsAPF M N`.
- `apfIndex_finiteBase_eq_towerIndexFactor` and `apfIndex_eq_mul_finiteBase`: for `u ≥ 0`, `apfIndex K N u = apfIndex K M u * apfIndex M N (apfPsi K M u)`, with no APF hypothesis on `N`.
- `IsAPF.hasDerivAt_apfPsi`, `IsAPF.exists_apfPsi_derivative_countable`: for an APF extension `L/K`, `apfPsi K L` has derivative `apfHerbrandSlope K L u` at every continuity point of the slope, hence outside a countable set. These two need no perfect residue field.
- `IsAPF.apfPsi_finiteBase_comp`: if `N/K` is APF, then `apfPsi M N (apfPsi K M u) = apfPsi K N u` for every real `u`; the base `M` need not be normal over `K`.

## Proofs

The comparison of upper groups is `absoluteGaloisBaseChange_mem_upper_iff`. The APF equivalence follows because a subgroup has finite index exactly when its preimage under a homomorphism with image of finite index does. Transitivity of `ψ` follows from the chain rule, the index formula, and the fundamental theorem of calculus.

## What to watch for

- `M` is an intermediate field of `SeparableClosure K`, finite over `K`; the versions for an abstract normed finite extension are in the module on strict APF under finite base change.
- `ψ` and the index are the library's functions `apfPsi` and `apfIndex`, defined from subgroups of the absolute Galois group.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseChange/Basic.lean` (SHA-256 of the source file `08f011f307b97a089730626841e98b0144a025ca11941f929347b13252c75e15`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
