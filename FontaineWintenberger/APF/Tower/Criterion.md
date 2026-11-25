# The APF criterion for elementary towers

Module `FontaineWintenberger.APF.Tower.Criterion`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field. Given an increasing sequence `E n` of finite subfields of the separable closure whose successive steps are elementary of levels `i n`, put `b n = apfPhi K (E n) (i n)` (the levels transformed to the upper numbering over `K`). The file proves Wintenberger's criterion 1.4.2: the union of the tower is APF exactly when `b n` tends to infinity, and gives a formula for `b n`.

## Definitions

- `FiniteIntermediateField.ramificationIdx K E`: the ramification index over `𝒪[K]` of the maximal ideal of `spectralIntegerRing K E`.
- `IsElementaryStep K E F hEF i`: for finite subfields `E ≤ F`, the extension `F/E` is `IsElementary` of level `i`, where `E` carries the spectral norm from `K` as its complete discretely valued structure.

## Results

For one elementary step `F/E` of level `i`: `level_pos` (`0 < i`), `apfPhi_pos`, `apfPhi_lt` (`apfPhi K E i < apfPhi K F j` for `i < j`), `apfPhi_eq` (`apfPhi K F i = apfPhi K E i`), `apfSubgroup_eq` (the APF products of `F` and `E` agree for `-1 ≤ u ≤ apfPhi K E i`), `apfSubgroup_eq_fixingSubgroup` (above that value the product of `F` is its fixing subgroup, if `G_K^u` fixes `E`). Conversely `isElementaryStep_of_apfSubgroup_profile` produces an elementary step from a one-jump profile of APF products.

For a tower, with `i` strictly increasing and `E 0` fixed by all `G_K^u`, `u > 0`:

- `elementary_tower_profiles`: `b` is strictly increasing, the products of `E (n+1)` and `E n` agree up to `b n`, and beyond `b n` the product of `E (n+1)` is its fixing subgroup.
- `isAPF_iSup_iff_tendsto_of_isElementaryStep` (`E` strictly increasing): the union is APF iff `b n → ∞`.
- `apfFiniteStage_iSup_eq_of_isElementaryStep`: for `b n < u ≤ b (n+1)` the finite stage of the union at `u` is `E (n+1)`.
- `apfPhi_zero_of_isElementaryStep`, `apfPhi_succ_sub_of_isElementaryStep`, `apfPhi_eq_sum_of_isElementaryStep`: `b n = i 0 / e(E 0) + Σ (i (k+1) − i k) / e(E (k+1))`, summed over `k < n`, with `e` the ramification index above; this is the weighted sum of Wintenberger's Remark 1.4.2.
- `isAPF_iSup_iff_tendsto_of_elementary_tower`: for `IsPerfectResidueLocalField K`, the same criterion with tameness of `E 0` stated as: the residue characteristic is coprime to `e(E 0)`.

## Proofs

The criterion follows from `isAPF_iSup_iff_tendsto_of_step_profiles`, applied to the profiles of `elementary_tower_profiles`.

## Points to watch

- The tower starts at Wintenberger's tame field `K₁`; the unramified field `K₀` is contained in `E 0`.
- Tameness of `E 0` is expressed in the main statements through upper ramification groups; only the last theorem uses the ramification index.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Criterion.lean` (SHA-256 of the source file `07ce29b06b8071d1cb17007c6e9274c1b7c855b6c04f2b7dfd3287930cd38e2f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
