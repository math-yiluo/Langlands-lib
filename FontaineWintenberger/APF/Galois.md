# The APF condition for a Galois extension, in its own Galois group

Module `FontaineWintenberger.APF.Galois`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field and `L/K` a Galois extension, possibly infinite, with upper ramification groups `upperRamificationGroupInfinite K L u`, written `Gal(L/K)^u`.

- `isAPF_iff_upperInfinite_finiteIndex`: `IsAPF K L` if and only if `Gal(L/K)^u` has finite index in `Gal(L/K)` for every `u ≥ -1`.
- `isAPF_iff_upperInfinite_isOpen`: equivalently, every such group is open in the Krull topology.
- `apfIndex_eq_upperInfiniteRelIndex`: for `u ≥ 0`, `apfIndex K L u` is the relative index of `Gal(L/K)^u` in `Gal(L/K)^0`.

For a Galois intermediate field `L` of `SeparableClosure K`: `apfSubgroup_eq_comap_upperInfinite` (the APF subgroup is the preimage of `Gal(L/K)^u` under restriction), `apfInertiaIndex_eq_upperInfiniteRelIndex`, `isAPFSubextension_iff_upperInfinite_finiteIndex`. `isOpen_upperRamificationGroupInfinite_iff_finiteIndex` (open if and only if of finite index) needs no perfect residue field.

The proofs use that restriction from the absolute Galois group is onto and maps upper groups onto upper groups.

To watch for: both indices are natural numbers, `0` when infinite.

Reference: Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Galois.lean` (SHA-256 of the source file `cebbfeb4f7cdf511283ad65921413b5bc8bd52cebdb45fa3ea634384bcbbc4f8`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
