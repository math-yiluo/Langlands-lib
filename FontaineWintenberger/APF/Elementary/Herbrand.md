# Herbrand functions of an elementary extension

Module `FontaineWintenberger.APF.Elementary.Herbrand`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field and `L/K` an elementary extension of level `i` (`IsElementary K L i`), of degree `n`. The file computes its index `apfIndex K L` and its functions `ψ = apfPsi K L`, `φ = apfPhi K L`.

- `IsElementary.apfIndex_eq_one`, `IsElementary.apfIndex_eq`: for `u ≥ 0`, the index is `1` if `u ≤ i` and `n` otherwise.
- `IsElementary.apfPsi_eq_self`, `IsElementary.apfPsi_eq`: `ψ(u) = u` if `u ≤ i`, and `ψ(u) = i + n (u - i)` otherwise.
- `IsElementary.apfPhi_eq`: `φ(u) = u` if `u ≤ i`, and `φ(u) = i + (u - i) / n` otherwise.

The index is read off the definition: `G_L · G_K^u` is the whole group up to `i` and is `G_L` beyond. The formulas follow from `apfPsi_eq_of_index_profile` and `apfPhi_eq_of_index_profile`, in the module on prime degree.

To watch for: `IsElementary.apfPhi_eq` takes `IsAPF K L` as an instance argument.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§1.3–1.4.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/Herbrand.lean` (SHA-256 of the source file `8fa1cfa085ba5c4fa569129c5036d8192805db0a686505dc5141ff6d4acfcf29`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
