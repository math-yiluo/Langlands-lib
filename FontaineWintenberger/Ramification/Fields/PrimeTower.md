# Towers of cyclic extensions of prime degree

Module `FontaineWintenberger.Ramification.Fields.PrimeTower`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a finite Galois extension `L/K`, chains of subgroups with normal steps of prime index give towers of intermediate fields with cyclic steps of prime degree.

- `isGalois_extendScalars_of_fixing_normal`: for intermediate fields `M ≤ N`, if the fixing subgroup of `N` is normal in that of `M`, then `N/M` is Galois.
- `cyclic_prime_extendScalars_of_fixing_step`: if moreover the index is a prime `p`, then `N/M` is Galois of degree `p` with cyclic Galois group.
- `relative_prime_field_chain`: if `E ≤ M` and the fixing subgroup of `E` is a `p`-group, then `E` and `M` are joined by a finite chain of such steps, stated with `Relation.ReflTransGen`.
- `wild_relative_prime_field_chain`: for `K` complete discretely valued, `p` the residue characteristic, and `M` containing the fixed field of the first lower ramification group, such a chain joins that fixed field to `M`.

The chain of subgroups and the `p`-group property of the first lower group come from earlier files.

## What to watch for

The relative extension `N/M` is `IntermediateField.extendScalars`.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Fields/PrimeTower.lean` (SHA-256 of the source file `be2f5841f339762ed4e685f9ab16273692b0c61ad7b953a3d09b258884aed32c`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
