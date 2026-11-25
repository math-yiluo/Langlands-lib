# Total ramification above the wild fixed field

Module `FontaineWintenberger.Ramification.Fields.Wild`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field (in the library's sense) with perfect residue field, `L` a finite Galois extension given as an ultrametric normed `K`-algebra, and `P` the first lower ramification group of `Gal(L/K)`. Above the fixed field `L^P`, every intermediate extension is totally ramified.

- `wildField_lower_zero_eq_top`: if `L^P ≤ M`, the zeroth lower ramification group of `Gal(L/M)`, computed on `spectralIntegerRing M L`, is the whole group.
- `wildField_top_ramificationIdx_eq_finrank`: then the ramification index of `spectralIntegerRing M L` over `𝒪[M]` equals `[L : M]`.
- `wildField_step_ramificationIdx_eq_finrank`: for `M ≤ N` with `L^P ≤ M`, the ramification index of `N/M` equals `[N : M]`.

The first rests on `finiteBase_lower_zero_eq_top`, from an earlier file.

## What to watch for

`M` is a complete discretely valued field through local instances; `N` over `M` is `IntermediateField.extendScalars`. `L` carries a norm here.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Fields/Wild.lean` (SHA-256 of the source file `8e8485d39f2f1ac53d7fa8aef1c879aa4c04950410e7c59513e5afa16d51d1f0`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
