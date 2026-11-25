# Upper ramification groups of infinite Galois extensions

Module `FontaineWintenberger.Ramification.Infinite.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field in the library's sense and `Ω` a field extension of `K`. The file defines the upper ramification subgroups of `Ω ≃ₐ[K] Ω` as the automorphisms whose restriction to every finite Galois subextension lies in the upper ramification group there, and shows that, for `Ω/K` Galois and the residue field of `K` perfect, each finite upper group is the image of the infinite one.

## Definition

`upperRamificationGroupInfinite K Ω u`: the intersection, over all `E : FiniteGaloisIntermediateField K Ω`, of the preimages under `AlgEquiv.restrictNormalHom E` of `upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u`. `mem_upperRamificationGroupInfinite` unfolds membership.

## Results

Without further hypotheses:

- `upperRamificationGroupInfinite_normal`: the subgroup is normal (an instance).
- `upperRamificationGroupInfinite_antitoneOn`: it is decreasing in `u` on `[−1, ∞)`; `upperRamificationGroupInfinite_neg_one`: at `u = −1` it is everything.
- `isClosed_upperRamificationGroupInfinite`: it is closed for the Krull topology.
- `map_upperRamificationGroupInfinite_le`: its image in `E ≃ₐ[K] E` lies in the finite upper group.

With `Ω/K` Galois: `isCompact_upperRamificationGroupInfinite`.

With moreover the residue field of `K` perfect, and `u ≥ −1`:

- `exists_lift_finite_upper_conditions`: given `q` in the upper group of a finite Galois `E` and a finite set `S` of finite Galois subextensions, some `s ∈ Gal(Ω/K)` restricts to `q` on `E` and to an element of the upper group on every `D ∈ S`.
- `exists_lift_upperRamificationGroupInfinite`: every such `q` is the restriction of an element of `upperRamificationGroupInfinite K Ω u`.
- `map_upperRamificationGroupInfinite`: the image of `upperRamificationGroupInfinite K Ω u` in `E ≃ₐ[K] E` equals the upper group of `E/K`.
- `mem_upperRamificationGroupInfinite_iff_cofinal`: if a family `E j` of finite Galois subextensions is cofinal (every finite Galois `D` lies in some `E j`), membership can be tested on the `E j` alone. Here `Ω/K` is not assumed Galois.

## Proofs

The finite lifting passes to the compositum `M` of `E` and the fields of `S` and uses that upper groups of `M/K` map onto those of its Galois subextensions (`finGaloisGroupMap_map_upperRamificationGroup`, the compatibility of upper numbering with quotients proved earlier). The full lifting follows by compactness of `Gal(Ω/K)`: the closed sets cut out by the conditions have the finite intersection property.

## What to watch for

- The definition is made for any field extension `Ω/K`; the surjectivity results need `IsGalois K Ω` and a perfect residue field.
- The parameter `u` is real, with statements restricted to `u ≥ −1`.
- The finite groups are computed on `spectralIntegerRing K E`, the library's ring of integers of `E`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Infinite/Basic.lean` (SHA-256 of the source file `4b8f4d47509176bf17333f93ec1e0ee70995962fb6725622d56b1a4f94cb7e9f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
- The file did not compile on the Library's Mathlib, which is older than the one the source was written for, and was repaired: Used Subgroup.coe_comap to express the closedness goal as a set preimage so that the restriction map's continuity proof applies.
