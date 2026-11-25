# Finite subfields stable under every automorphism

Module `FontaineWintenberger.Mathlib.FieldTheory.NormalClosure`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be a field extension and `D` an intermediate field. Mathlib's `normalClosure K D L` is the compositum inside `L` of the images of all `K`-embeddings `D → L`. The file shows that it is stable under the automorphisms of `L/K`, with no normality hypothesis on `L`.

## Main definitions and results

- `IntermediateField.map_normalClosure_le`: a `K`-algebra endomorphism `σ` of `L` maps `normalClosure K D L` into itself.
- `IntermediateField.map_normalClosure_eq`: a `K`-automorphism `σ` of `L` maps it onto itself.
- `IntermediateField.normalClosureRestrict D σ`: the automorphism of `normalClosure K D L` induced by `σ` (`coe_normalClosureRestrict`).
- `IntermediateField.exists_finite_aut_stable`: if `D` is finite over `K`, some intermediate field `E ⊇ D`, finite over `K`, satisfies `σ(E) = E` for every `K`-automorphism `σ` of `L`.

## Points to watch

- As `L/K` is not assumed normal, `normalClosure K D L` need not be normal over `K`; only stability under automorphisms of `L` is proved.
- The declarations are in Mathlib's namespace `IntermediateField`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/FieldTheory/NormalClosure.lean` (SHA-256 of the source file `70a4c134ecc336b128c595fd7db5ca456504bd11a0a2bba2b271602a3a922832`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
