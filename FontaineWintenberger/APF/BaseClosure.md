# Separable closures and Galois groups after a change of base

Module `FontaineWintenberger.APF.BaseClosure`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

This file is pure field theory: `K` is any field and `M` an intermediate field of `SeparableClosure K`. It identifies the separable closure and the absolute Galois group of `M` with objects built from `SeparableClosure K`, and compares finite Galois layers over `K` and over `M`.

## Definitions

- `separableClosureBaseChangeEquiv K M`: an `M`-algebra isomorphism `SeparableClosure M ≃ SeparableClosure K`, obtained from uniqueness of separable closures; `isSepClosure_over_subextension` says that `SeparableClosure K` is a separable closure of `M`.
- `absoluteGaloisBaseChangeEquiv K M`: the group isomorphism from the automorphism group of `SeparableClosure M` over `M` onto the fixing subgroup of `M` in the automorphism group of `SeparableClosure K` over `K`.
- `finiteGaloisNormalClosure K D`: the normal closure in `SeparableClosure K` of a finite intermediate field `D`, as a `FiniteGaloisIntermediateField`.
- `finiteGaloisLayerOverBase K M E hME`: a finite Galois intermediate field `E` over `K` that contains `M`, regarded as a finite Galois intermediate field over `M`.

## Results

- `coe_absoluteGaloisBaseChangeEquiv`, `absoluteGaloisBaseChangeEquiv_apply`: the isomorphism of groups is conjugation by the isomorphism of closures.
- `le_finiteGaloisNormalClosure`: the normal closure contains `D`.
- `exists_finiteGalois_over_base_layer` (for `M` finite over `K`): every finite Galois layer over `M` lies in a finite Galois layer over `K` that contains `M`.
- `exists_finiteGalois_containing_base` (for `M` finite over `K`): every finite Galois layer over `K` lies in one that contains `M`.
- `finiteGaloisLayerOverBase_restrictScalars`: rebasing does not change the underlying field.

## What to watch for

The isomorphism of separable closures is a choice, not canonical; the results stated about it hold for the chosen one. No valuation or topology enters this file.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/BaseClosure.lean` (SHA-256 of the source file `de50cf6cd0d10443df27252f9b8e52fc4641926ace2a61c80d850838c717ced8`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
