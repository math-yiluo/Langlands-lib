# Finite stages of an APF extension

Module `FontaineWintenberger.APF.Tower.Stages`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `L` an intermediate field of its separable closure. For a real parameter `u`, the stage `apfFiniteStage K L u` is the fixed field of the APF product `apfSubgroup K L u` (the subgroup `G_L G_K^u`). When `L/K` is APF these stages are finite over `K`, increase with `u` and exhaust `L`. The file establishes this, pulls the stages back to abstract separable extensions, and bounds from below the ramification bounds of steps between large finite layers.

## Definition

`apfFiniteStage K L u`: `IntermediateField.fixedField (apfSubgroup K L u)`.

## Results

- `exists_absoluteUpper_le_fixingSubgroup_of_finite`: for a finite subfield `M` there is `U ≥ 0` such that the upper ramification group `G_K^u` fixes `M` for all `u ≥ U`.
- `fixingSubgroup_apfFiniteStage`: the fixing subgroup of the stage is exactly `apfSubgroup K L u`, because that subgroup is closed.
- `apfFiniteStage_le`, `apfFiniteStage_mono`: the stage is contained in `L`, and stages increase with `u` on `u ≥ -1`.
- `finiteDimensional_apfFiniteStage`: if `L` is APF (`IsAPFSubextension K L`) and `u ≥ -1`, the stage is finite over `K`.
- `exists_le_apfFiniteStage`: every finite subfield of `L` lies in all stages with `u` large.

For an abstract separable APF extension `L/K` with an embedding `j` into the separable closure:

- `exists_finiteIntermediateField_map_eq_apfFiniteStage`: for `u ≥ -1` there is a finite intermediate field `E` of `L` with `j(E)` equal to the stage of `j(L)` at `u`.
- `IsAPF.exists_finiteIntermediateField_ge_map_eq_apfFiniteStage`: such `E` can be taken above any given finite intermediate field.
- `IsAPF.exists_monotone_cofinal_finiteIntermediateFields_map` and `IsAPF.exists_monotone_cofinal_finiteIntermediateFields`: the stages at integer parameters give a monotone sequence `E : ℕ → FiniteIntermediateField K L` that is cofinal among all finite intermediate fields.

With the residue field of `K` perfect:

- `apfPsi_le_relativeFirstBound_of_apfFiniteStage_le`: for finite intermediate fields `E ≤ F` of `L` with `j(E)` containing the stage at `u ≥ 0`, `apfPsi K E u ≤ apfRamificationBound E F`, where `E` carries the spectral norm.
- `IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge`: for `L/K` APF and any real `c`, there is a finite `T` such that `c ≤ apfRamificationBound E F` for all finite `T ≤ E ≤ F`.

## Proofs

Finiteness of a stage is openness of its fixing subgroup. The lower bound on relative ramification bounds uses a comparison of APF products under finite base change.

## Points to watch

- The stages are defined for every `L` and `u`; finiteness needs the APF hypothesis and `u ≥ -1`.
- The ramification bound takes values in `EReal`; for a trivial step `E = F` it is `⊤`, and the last theorem includes that case.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Stages.lean` (SHA-256 of the source file `93c173a0441ee5a669a421cf7f49c21edd24d8e83a1771f4b038141f397f3fb7`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
