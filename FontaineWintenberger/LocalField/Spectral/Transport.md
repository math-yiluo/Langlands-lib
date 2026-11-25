# Transport between equal valuation subrings

Module `FontaineWintenberger.LocalField.Spectral.Transport`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a field with `IsCompleteDiscreteValuedField K`, `L/K` a finite extension, and `w` a valuation on `L` extending the norm valuation of `K`.

The file contains one definition, `spectralIntegerRingAlgEquivOfEq`: given a proof `h` that `spectralIntegerRing K L = w.valuationSubring` as valuation subrings of `L`, it is the isomorphism of `𝒪[K]`-algebras between the two rings induced by the identity of `L`.

The equality `h` is a hypothesis here; the file does not prove it.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Spectral/Transport.lean` (SHA-256 of the source file `494c27ce7a76222117c9dc8215536a12be2624c4e02b102239f6815eed98616e`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
