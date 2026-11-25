# Residue degrees of the finite stages of an APF extension

Module `FontaineWintenberger.APF.Tower.Residue`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field `k`. The file shows that the index of the APF product at parameter zero, `apfSubgroup K M 0` (the subgroup `G_M G_K^0`), is the residue degree of a finite separable extension `M/K`, and deduces that in an APF extension the residue fields of finite subextensions stabilize.

## Results

- `apfSubgroup_index_zero_eq_residueDegree_of_finiteGalois`: for a finite Galois extension `Ω/K`, an intermediate field `M` and an embedding `j` of `Ω` into the separable closure, the index of `apfSubgroup K (j(M)) 0` equals the degree over `k` of the residue field of `spectralIntegerRing K M`.
- `apfSubgroup_index_zero_eq_residueDegree`: the same for any finite separable `M/K` with an embedding `j : M →ₐ[K] SeparableClosure K`.
- `apfSubgroup_zero_eq_of_apfFiniteStage_le`: for intermediate fields `E ≤ L` of the separable closure with `apfFiniteStage K L 0 ≤ E`, `apfSubgroup K E 0 = apfSubgroup K L 0`.
- `residueDegree_eq_zeroStage_of_apfFiniteStage_le`: if `L` is APF (`IsAPFSubextension K L`) and `E` is finite with `apfFiniteStage K L 0 ≤ E ≤ L`, then `E` and the zero stage have the same residue degree over `k`.
- `spectralResidueInclusion_zeroStage_surjective`, `spectralResidueInclusion_surjective_of_zeroStage_le`: for finite `E ≤ F ≤ L` above the zero stage, the residue map `spectralResidueInclusion` from `E` to `F` is surjective; neither field need be normal.
- `IsAPF.exists_finiteIntermediateField_residueDegree_stable`: for an abstract separable APF extension `L/K` there is a finite intermediate field `E₀` such that every finite `F ≥ E₀` has the residue degree of `E₀`.
- `IsAPF.exists_finiteIntermediateField_residueInclusion_surjective`: there is a finite `E₀` such that for all finite `E₀ ≤ E ≤ F` the residue inclusion from `E` to `F` is surjective.

## Proofs

In a finite Galois overfield the index is computed from the upper ramification group at `0`, which is the lower ramification group at `0`, and the index of the orbit under inertia is the residue degree (results from the files on nonnormal finite extensions and on ramification groups). The general finite case passes to the normal closure inside the separable closure. Equal residue degrees and injectivity of the residue map give surjectivity by a dimension count. The abstract statements pull the zero stage back along an embedding of `L` (`exists_finiteIntermediateField_map_eq_apfFiniteStage`).

## Points to watch

- The index here is the full index of `apfSubgroup K M 0` in the absolute Galois group; it keeps the residue factor that the inertia-relative index `apfIndex` omits.
- The residue field of `K` is assumed perfect throughout, except in `apfSubgroup_zero_eq_of_apfFiniteStage_le`.
- Residue fields of finite layers are those of `spectralIntegerRing K E`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Residue.lean` (SHA-256 of the source file `ceb54b6615fdd30a81ff00d8c3fdfb2af574f912b4981b57c719758a81f8c919`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
