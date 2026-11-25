# The first ramification bound i(L/K)

Module `FontaineWintenberger.APF.RamificationBound`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a complete discretely valued field `K` and a separable extension `L/K`, the file defines Wintenberger's bound `i(L/K)` as an extended real number.

`apfRamificationBound K L : EReal` is the supremum of the real numbers `u ≥ -1` such that `G_L · G_K^u = G_K`, that is `apfSubgroup K i.fieldRange u = ⊤`, where `i` is the embedding `IsSepClosed.lift` of `L` in `SeparableClosure K`.

Results:

- `apfSubgroup_fieldRange_index_eq`, `apfSubgroup_fieldRange_eq_top_iff`: the index of `apfSubgroup`, and its being the whole group, do not depend on the embedding, since two embeddings are conjugate;
- `apfRamificationBound_eq_embedding`: the bound may be computed with any embedding;
- `le_apfRamificationBound`: every admissible `u` is below the bound;
- `neg_one_le_apfRamificationBound`: the bound is at least `-1`;
- `apfRamificationBound_algEquiv`: invariance under `K`-isomorphism;
- `apfRamificationBound_self`: the bound of `K/K` is `⊤`.

The bound takes the value `⊤` when the admissible parameters are unbounded. No APF hypothesis is made.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/RamificationBound.lean` (SHA-256 of the source file `d6da65de2af239e941cdc3cd6ffecae0fdf1abe45045f8118f8aff72db601af2`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
