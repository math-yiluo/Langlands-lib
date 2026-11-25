# Total ramification in a tower of discrete valuation rings

Module `FontaineWintenberger.Ramification.Lower.TotalRamification`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file contains one theorem on a tower `R → S → T` of discrete valuation rings, where the maps are local and injective (`FaithfulSMul`), and `S` is finite over `R` and `T` finite over `S`.

`ramificationIdx_eq_finrank_tower_iff`: the ramification index of the maximal ideal of `T` over `R` equals the rank of `T` over `R` if and only if the same holds for `S` over `R` and for `T` over `S`. In words, `T/R` is totally ramified exactly when both steps are.

The proof rewrites each of the three conditions, by `ramificationIdx_eq_finrank_iff_residue_surjective` from the file on degrees, as surjectivity of the map of residue fields. The map of residue fields of `T/R` factors through that of `S`, and the second factor is injective, so the composite is onto exactly when both factors are.

Here "totally ramified" is expressed as the equality of the ramification index with the rank of the module; no separability of residue fields and no completeness is assumed.

Reference: Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/TotalRamification.lean` (SHA-256 of the source file `9f0f5e75ba3989fc10554b1fb24dde81034b05d91a045866b8d53829331dfadc`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
