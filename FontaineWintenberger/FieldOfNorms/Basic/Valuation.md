# The valuation of the field of norms

Module `FontaineWintenberger.FieldOfNorms.Basic.Valuation`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` a separable APF extension. Each finite intermediate field `E` has a normalized discrete valuation, attached to the maximal ideal of `spectralIntegerRing K E`. The file shows that on large finite layers these valuations of the coordinates of an element of `FieldOfNorms K L` no longer depend on the layer, and defines the valuation of the field of norms as this common value.

## Definitions

- `FieldOfNorms.coordinateValuation K L E`: the monoid-with-zero homomorphism from `FieldOfNorms K L` to `WithZero (Multiplicative ℤ)` sending `x` to the normalized valuation of its coordinate at `E`. It is defined for every separable `L/K`.
- `FieldOfNorms.valuation K L`: `coordinateValuation` at a finite intermediate field chosen from the stability theorem below; it requires `L/K` APF.

## Results

- `FiniteIntermediateField.normalizedValuation_norm_of_residueInclusion_surjective`: for finite intermediate fields `E ≤ F` whose residue map `spectralResidueInclusion` is surjective, the normalized valuation in `E` of the norm of `x` from `F` to `E` equals that of `x` in `F`. No normality is assumed.
- `FieldOfNorms.exists_coordinateValuation_stable`: there is a finite `E₀` such that `coordinateValuation` at `E` and at `F` agree for all finite `E, F ≥ E₀`.
- `FieldOfNorms.exists_valuation_eq_coordinateValuation`: there is a finite `E₀` such that `FieldOfNorms.valuation` equals `coordinateValuation` at every finite `E ≥ E₀`.
- `FieldOfNorms.valuation_eq_zero_iff`: the valuation of `x` is `0` iff `x = 0`.
- `FieldOfNorms.valuation_eq_coordinate_of_maximalUnramified_le` (for `IsPerfectResidueLocalField K`): the valuation is computed by `coordinateValuation` at every finite `E` containing `apfMaximalUnramified K L`, as in Wintenberger, paragraph 2.1.2.

## Proofs

The valuation of a norm is the valuation raised to the residue degree; when the residue map is surjective the residue degree is `1`. In an APF extension the residue maps between finite layers are surjective on a tail (`IsAPF.exists_finiteIntermediateField_residueInclusion_surjective`), and the coordinates of an element are related by norms, so comparing two layers through their compositum gives stability. The last statement uses surjectivity of residue maps above the maximal unramified subfield.

## Points to watch

- `FieldOfNorms.valuation` is only a multiplicative map here (`→*₀`), not a `Valuation`: the ultrametric inequality needs the addition and is proved in a later file.
- It is defined by choice of a stable layer; the theorems above make it independent of that choice.
- Values lie in `WithZero (Multiplicative ℤ)`, so the valuation is written multiplicatively and integral elements are those of value at most `1`.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§2–3, in particular paragraph 2.1.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Basic/Valuation.lean` (SHA-256 of the source file `5b4d1d343054d4cbff2587c23a043454dd293f3db78a45c248022274fd72afc7`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
