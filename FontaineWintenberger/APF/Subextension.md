# APF and strict APF under subextensions and finite extensions

Module `FontaineWintenberger.APF.Subextension`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field. The file compares the APF invariants of two separable extensions of `K`, one contained in the other: the Herbrand integral `apfPsi`, the strictness ratio, the ramification bound and the strictness constant. It concludes that strict APF passes to subextensions, and that APF and strict APF are unchanged by a finite extension on top.

## Results for intermediate fields `M ≤ N` of the separable closure

- `apfPsi_le_towerIndexFactor_mul`: for `N` APF and `u ≥ 0`, `apfPsi K N u ≤ apfTowerIndexFactor K M N u · apfPsi K M u`.
- `apfStrictnessRatio_le_of_le`: under the same hypotheses the strictness ratio of `N` is at most that of `M`.
- `IsStrictlyAPF.of_le`: if `N` is strictly APF, so is `M`; no normality is assumed.
- `apfRamificationBound_le_of_le`: `apfRamificationBound K N ≤ apfRamificationBound K M`.
- `apfStrictnessConstant_le_of_le`: for `N` APF with `0 < apfRamificationBound K N`, the strictness constant of `N` is at most that of `M`.

When moreover `N` is finite over `M` (stated as `FiniteDimensional M (IntermediateField.extendScalars hMN)`):

- `isAPFSubextension_finiteExtension_iff`: `IsAPFSubextension K N ↔ IsAPFSubextension K M`.
- `apfTowerIndexFactor_le_inertiaFixingRelIndex`: the tower factor is bounded, uniformly in `u`, by the relative index of `N.fixingSubgroup ⊓ G_K^0` in `M.fixingSubgroup ⊓ G_K^0`, which is positive (`inertiaFixingRelIndex_pos`).
- `apfPsi_mono_extension`: `apfPsi K M u ≤ apfPsi K N u` for `u ≥ 0` (this one needs only `N` APF).
- `apfStrictnessRatio_le_finiteExtension_mul`: the ratio of `M` is at most that index times the ratio of `N`.
- `isStrictlyAPF_finiteExtension_iff`: `IsStrictlyAPF K N ↔ IsStrictlyAPF K M`, also for non-normal extensions.

## Results for abstract separable extensions

For a `K`-algebra map `f : P →ₐ[K] L` of separable extensions: `IsStrictlyAPF.of_algHom`, `apfRamificationBound_le_of_algHom`, `apfStrictnessConstant_le_of_algHom` restate the first group. For a tower `K ⊆ P ⊆ L` with `L` finite over `P`: `isAPF_finite_extension_iff` and `isStrictlyAPF_finite_extension_iff`.
## Proofs

The index of `N` factors as the index of `M` times the tower factor (`apfIndex_eq_mul_towerIndexFactor`), and the factor is monotone in `u`; integrating gives the bound on `apfPsi`. For finite extensions, the relative index of fixing subgroups is positive, so the tower factor is bounded, and the lower limit of the ratio of `N` is at least a positive multiple of that of `M`. The abstract statements are reduced to intermediate fields by choosing an embedding into `SeparableClosure K` and using invariance under isomorphism.

## Points to watch

- The comparisons of strictness constants require a positive ramification bound for the larger field.
- "Finite extension" always means the upper step `N/M` (or `L/P`) is finite; `M` and `N` may be infinite over `K`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Subextension.lean` (SHA-256 of the source file `edf41cd0b9ecff0f7cb5737f79a6d27d372281e5b6699504f7d1fa3bad016481`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
