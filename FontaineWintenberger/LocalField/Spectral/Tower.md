# Normed field extensions and intermediate fields

Module `FontaineWintenberger.LocalField.Spectral.Tower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file records that a normed algebra between ultrametric normed fields gives an extension of their norm valuations, and transfers to the unit ball of a finite separable normed extension the results proved for valuation rings of compatible extensions.

## Main results

- Instance `NormedField.valuation_hasExtension`: for ultrametric normed fields `K`, `L` with `L` a normed `K`-algebra, the norm valuation of `L` extends that of `K`.
- Instance `IntermediateField.normedAlgebraAmbient`: `L` is a normed algebra over any intermediate field `F`, with the inherited norm.
- `IntermediateField.completeSpace_of_finiteDimensional`: if `K` is complete and `L/K` is finite, every intermediate field is complete.

For `K` with `IsCompleteDiscreteValuedField K` and `L` an ultrametric normed field, finite and separable over `K` as a normed algebra:

- `normedAlgebra_unitBall_isDiscreteValuationRing`, `normedAlgebra_unitBall_henselianLocalRing`: `𝒪[L]` is a Henselian discrete valuation ring.
- `normedAlgebra_unitBall_exists_generator`: if `𝓀[K]` is perfect, `𝒪[L]` is generated over `𝒪[K]` by one element.
- `normedAlgebra_isCompleteDiscreteValuedField`: `L` (nontrivially normed) satisfies `IsCompleteDiscreteValuedField`.

These follow from the corresponding statements `extensionValuationSubring_…` for a valuation extending that of `K`.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Spectral/Tower.lean` (SHA-256 of the source file `892bd5e5c2b85c6ae69fbe2dc7675bdbb010158249151ef41ae9e5d56e442a73`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
