# Suprema with a decreasing intersection of closed subgroups

Module `FontaineWintenberger.Mathlib.Topology.CompactGroupSup`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file proves one statement about compact topological groups: joining with a closed normal subgroup commutes with a decreasing countable intersection of closed subgroups.

`Subgroup.iInf_sup_eq_iInf_sup_of_isClosed`: let `G` be a compact topological group, `H : ℕ → Subgroup G` an antitone sequence of closed subgroups, and `U` a closed normal subgroup. Then `(⨅ n, H n) ⊔ U = ⨅ n, (H n ⊔ U)`.

The inclusion from left to right is formal. For the other, take `g` in every `H n ⊔ U`; the sets `{h ∈ H n | h⁻¹ * g ∈ U}` are nonempty (by normality of `U`), closed, and decreasing, so by compactness their intersection is nonempty, and a common point `h` gives `g = h * (h⁻¹ * g)`.

## What to watch for

- The index set is `ℕ`: the statement is for sequences, not arbitrary directed families.
- `G` is not assumed Hausdorff or profinite; `U` must be normal.
- The theorem lies in Mathlib's `Subgroup` namespace.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/Topology/CompactGroupSup.lean` (SHA-256 of the source file `39769f9f56fec2a98a9ac1ac166755382a055313c6fdd3b93f756da9324feefb`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
