# Elementary extensions

Module `FontaineWintenberger.APF.Elementary.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K`, the file defines Wintenberger's elementary extensions: finite separable extensions with a single positive ramification break, not assumed normal.

`IsElementary K L i` is a structure of propositions: `L/K` is finite and separable, `0 < i`, and for every `K`-embedding `j` of `L` into `SeparableClosure K` the product `G_L · G_K^u`, that is `apfSubgroup K j.fieldRange u`, is the whole group `G_K` at `u = i` and equals the fixing subgroup of `j(L)` for every `u > i`.

Results:

- `IsElementary.of_embedding`: for `L/K` finite, it suffices to check the two conditions for one embedding;
- `IsElementary.apfSubgroup_eq_top_of_le`: the product is the whole group for `-1 ≤ u ≤ i`;
- `IsElementary.le_apfRamificationBound`: `i ≤ apfRamificationBound K L`;
- `IsElementary.apfRamificationBound_eq`: if the degree of `L/K` is greater than `1`, then `apfRamificationBound K L = i`.

The equality of the level with the first ramification bound carries the hypothesis `1 < Module.finrank K L`.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.3.1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Elementary/Basic.lean` (SHA-256 of the source file `14048feaa6e03a196f1214db261ebf108f770f5a397f1cad1f74c24eae487944`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
