# Uniqueness of the valuation ring of a finite separable extension

Module `FontaineWintenberger.LocalField.Spectral.Uniqueness`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsCompleteDiscreteValuedField K`, let `L/K` be finite separable, and let `w` be any valuation on `L` extending the norm valuation of `K` (`HasExtension`). The file proves that the valuation ring of `w` is the spectral integer ring, hence does not depend on `w`.

## Main results

- Instance `Valuation.HasExtension.valuationSubring_faithfulSMul`: for any extension of valuations of fields, the map of valuation rings is injective.
- `spectralIntegerRing_eq_extension_valuationSubring`: `spectralIntegerRing K L = w.valuationSubring`.
- Instances `extensionValuationSubring_isIntegralClosure`, `extensionValuationSubring_moduleFinite`: `w.valuationSubring` is the integral closure of `𝒪[K]` in `L`, finite over `𝒪[K]`.
- `extensionValuationSubring_isDiscreteValuationRing`, `extensionValuationSubring_henselianLocalRing`: it is a Henselian discrete valuation ring.
- `extensionValuationSubring_exists_generator`: if `𝓀[K]` is perfect, it is generated over `𝒪[K]` by one element.

## Proofs

Elements of the spectral integer ring are integral over `𝒪[K]`, hence lie in the valuation ring of `w`. By `ValuationSubring.eq_of_le_of_ne_top` the larger ring is equal to it or to `L`; the latter is excluded because a uniformizer of `K` is not a unit for `w`.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Spectral/Uniqueness.lean` (SHA-256 of the source file `e2e0c6137a1d37d30ab2371f30799018cb65ca8cf130cef4539c96da49990f5d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
