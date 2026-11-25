# Upper products across an elementary step

Module `FontaineWintenberger.APF.Tower.FiniteProfile`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, and `E ≤ F` intermediate fields of its separable closure with `E` finite over `K`. The field `E` carries the spectral norm, which makes it a complete discretely valued field, and `F` is viewed as an extension of `E` (`IntermediateField.extendScalars hEF`). The file translates the property that `F/E` is elementary of level `i` (`IsElementary`) into a statement about the APF products `apfSubgroup K F u` over `K`.

## Results

Assume `F/E` is `IsElementary` of level `i`.

- `apfSubgroup_eq_of_isElementary`: for `u ≥ -1` with `apfPsi K E u ≤ i`, `apfSubgroup K F u = apfSubgroup K E u`.
- `apfSubgroup_eq_fixingSubgroup_of_isElementary`: for `u ≥ -1` with `i < apfPsi K E u`, if the upper ramification group `G_K^u` fixes `E`, then `apfSubgroup K F u` is the fixing subgroup of `F`.
- `apfPsi_eq_of_isElementary`: `apfPsi K F u = apfPsi K E u` whenever `apfPsi K E u ≤ i`.
- `apfPhi_eq_of_isElementary` and `apfPhi_lt_of_isElementary` (`F` finite over `K`): `apfPhi K F i = apfPhi K E i`, and `apfPhi K E i < apfPhi K F j` for `i < j`.

Converse and related statements:

- `isElementary_of_apfSubgroup_profile` (`F` finite): if for some `b > 0` the product of `F` at `b` is the fixing subgroup of `E`, and for all `u > b` it is the fixing subgroup of `F`, then `F/E` is elementary of level `apfPsi K E b`.
- `apfRamificationBound_eq_of_apfSubgroup_jump`: if the product of `F` at `b > 0` is the fixing subgroup of `E` and differs from it at every `u > b`, then the ramification bound of `F` over `E` is `apfPsi K E b`. Here `F` may be infinite.
- `apfIndex_eq_ramificationIdx_of_absoluteUpper_le`: if `G_K^u` fixes `E` for some `u ≥ 0`, then `apfIndex K E u` is the ramification index of `E/K` (of the maximal ideal of `spectralIntegerRing K E` over `𝒪[K]`).
- `apfPsi_sub_of_absoluteUpper_le`: if `G_K^u` fixes `E` for all `u > a`, with `0 ≤ a ≤ b`, then `apfPsi K E b − apfPsi K E a = (b − a) · e(E/K)`.

## Proofs

The absolute Galois group of `E` is identified with the fixing subgroup of `E` inside that of `K` (`absoluteGaloisBaseChangeEquiv`). Under this identification the preimage of `apfSubgroup K F u` is the APF product of `F/E` at parameter `apfPsi K E u` (`comap_apfSubgroup_finiteBase`, from the file on finite base change).
## Points to watch

- The second result needs the extra hypothesis that `G_K^u` fixes `E`; it is not a consequence of elementarity alone.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/FiniteProfile.lean` (SHA-256 of the source file `8875b868def2b094fca1daa54b7f8f2f57db26f70fe4521fb2820436d4043e48`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
