# Residue fields of finite normed extensions

Module `FontaineWintenberger.LocalField.Residue.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued normed field (`IsCompleteDiscreteValuedField K`) and `M` an ultrametric normed field that is a finite separable normed `K`-algebra. The file studies the residue field `𝓀[M]` as an extension of `𝓀[K]`.

## Main results

- `normedAlgebra_residueField_finiteDimensional`: `𝓀[M]` is finite-dimensional over `𝓀[K]`.
- `normedAlgebra_residueField_perfectField`: if `𝓀[K]` is perfect, so is `𝓀[M]`.
- `normedAlgebra_isPerfectResidueLocalField`: if `K` satisfies `IsPerfectResidueLocalField` and `L` is a nontrivially normed ultrametric field, finite and separable over `K` as a normed algebra, then `L` satisfies `IsPerfectResidueLocalField`.
- `normedAlgebra_residueChar_eq`: in that situation `residueChar L = residueChar K`.

## Proofs

Finiteness of the residue extension follows from finiteness of the valuation ring of `M` as a module over `𝒪[K]` (`extensionValuationSubring_moduleFinite`). Perfectness passes to algebraic extensions. The last two results use `normedAlgebra_isCompleteDiscreteValuedField` and the equality of characteristics along an algebra map of fields.

## Points to watch

- The extension is assumed separable throughout, and no finiteness of residue fields is assumed.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Residue/Basic.lean` (SHA-256 of the source file `df4d277620a193e9a087a1cc0f3539a9a2b21b74447be8e4b01ae83c924ba239`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
