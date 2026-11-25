# The eventual slope of ψ for a finite extension

Module `FontaineWintenberger.APF.Finite.Slope`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `M/K` a finite separable extension. The file shows that the index `apfIndex K M u` is constant for large `u`, equal to the ramification index of `M/K`, so that `ψ = apfPsi K M` is eventually affine with that slope. Neither normality nor total ramification is assumed.

## Results without a hypothesis on the residue field

Here `M` is a finite intermediate field of `SeparableClosure K`.

- `fixingSubgroup_inertiaRelIndex_pos`: the relative index of the fixing subgroup of `M` in the absolute inertia group `G_K^0` is positive.
- `apfIndex_le_fixingSubgroup_inertiaRelIndex`: `apfIndex K M u` is at most that relative index, for every `u`.
- `exists_apfIndex_finite_constant`: there are a natural number `C > 0` and a real `b ≥ 0` with `apfIndex K M u = C` for all `u ≥ b`.
- `exists_apfPsi_finite_affine`: moreover `ψ(u) = ψ(b) + C (u - b)` for `u ≥ b`.

## Results with perfect residue field

- `intermediate_spectral_ramificationIdx_eq_relIndex`: for an intermediate field `M` of a finite Galois extension `L/K`, the ramification index of `spectralIntegerRing K M` over `𝒪[K]` is the relative index of the fixing subgroup of `M` in the inertia group of `Gal(L/K)`.
- `exists_intermediate_apfIndex_eq_ramificationIdx`: for such `M`, `apfIndex K M u` equals that ramification index for all `u` beyond some `U ≥ 0`.
- `exists_apfIndex_eq_spectral_ramificationIdx`: the same for an abstract finite separable extension `M/K`.
- `exists_apfPsi_spectral_ramificationIdx_affine`, `exists_apfPsi_spectral_ramificationIdx_shift`: beyond `U`, `ψ` is affine with slope the ramification index `e`: `ψ(u + h) = ψ(u) + e · h` for `u ≥ U`, `h ≥ 0`.
- For a normed field `M` with ultrametric norm and `NormedAlgebra K M`: `normed_ramificationIdx_eq_spectral` (the unit ball `𝒪[M]` and the spectral integer ring have the same ramification index over `𝒪[K]`), and the three statements above with the ramification index of `𝒪[M]`: `exists_apfIndex_eq_normed_ramificationIdx`, `exists_apfPsi_normed_ramificationIdx_affine`, `exists_apfPsi_normed_ramificationIdx_shift`.

## Proofs

The first group uses that the index is nondecreasing for an APF extension and bounded, hence eventually constant. The second uses that the upper ramification groups of a finite Galois group are eventually trivial, the formula for the index of an intermediate field inside a finite Galois extension, and the expression of the ramification index of a fixed field as a relative index; the abstract case passes to the normal closure.

## What to watch for

- The threshold `U` is only asserted to exist; the first group of results does not identify the constant `C`.
- In the statements for a normed field, the discrete valuation ring structure on `𝒪[M]` is introduced by `letI` inside the statement.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Finite/Slope.lean` (SHA-256 of the source file `032387c677190c9835b2bae122f60cbc5344409315302dcf42091d226eaec8ff`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
