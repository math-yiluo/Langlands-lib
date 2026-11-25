# Galois actions on the field of norms

Module `FontaineWintenberger.FieldOfNorms.Functor.Galois`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`. The file has two parts. First, for an infinite separable APF extension `L/K`, the action of `K`-automorphisms of `L` on `FieldOfNorms K L` is faithful. Second, for infinite separable APF extensions `M ⊆ N` of `K` with `N/M` finite Galois, the field of norms of `N` is a finite Galois extension of that of `M`, with the same Galois group and the same degree.

## Faithfulness

- `FieldOfNorms.mapEquiv_eq_self_iff`: `FieldOfNorms.mapEquiv σ` is the identity exactly when `σ = 1`. `L/K` need not be normal.
- `FieldOfNorms.aut_injective`: the homomorphism `FieldOfNorms.aut K L` is injective.
- `FieldOfNorms.uniformizerCoordinateInteger`: the coordinate at a finite intermediate field `E` of the uniformizer of the field of norms; `uniformizerCoordinateInteger_irreducible`: it is a uniformizer of `spectralIntegerRing K E` when `E` contains `apfMaximalUnramified K L`.
- `FiniteIntermediateField.aut_eq_of_mapEquiv_fixed`: if `σ` fixes every norm family, its restriction to each `σ`-stable finite `E` containing `apfMaximalTame K L` is the identity.

Proof: on such `E` the restriction fixes the coordinates of the residue constants, hence acts trivially on residues, and fixes the coordinate of the uniformizer; so it is the identity. Any element of `L` lies in a stable normal closure.

## The Galois extension of fields of norms

- `FieldOfNorms.mem_range_inclusion_iff_fixed`: a norm family of `N` lies in the image of `FieldOfNorms.inclusion K M N` exactly when all automorphisms of `N/M` fix it.
- `FieldOfNorms.autRestrictScalars`, `FieldOfNorms.galoisAction`: the action of `Gal(N/M)` on `FieldOfNorms K N`; it is faithful (`autRestrictScalars_injective`).
- `FieldOfNorms.isGaloisGroup`: Mathlib's `IsGaloisGroup (N ≃ₐ[M] N) (FieldOfNorms K M) (FieldOfNorms K N)`.
- `FieldOfNorms.finiteDimensional_of_isGalois`, `FieldOfNorms.isGalois`, `FieldOfNorms.finrank_of_isGalois`: the extension of fields of norms is finite, Galois, of degree `[N : M]`.
- `FieldOfNorms.autEquiv`: the group isomorphism from `Gal(N/M)` to the automorphism group of `FieldOfNorms K N` over `FieldOfNorms K M`.

Proof of descent: for a fixed family `β`, at each finite intermediate field `D` of `N/K` that is stable under `Gal(N/M)` and a "good layer" (`IsGoodFiniteLayer`), the coordinate of `β` is fixed, hence comes from a unique element of the pullback of `D` to `M` (`galoisNormCoordinate`). Such `D` are cofinal. Taking norms down from a chosen such field (`galoisGoodUpper`) defines a coordinate at every finite intermediate field of `M/K` (`galoisCoordinate`); these are independent of the choice and norm-compatible, and give an element `galoisNormDescent` whose inclusion is `β`. The Galois statements then follow from Mathlib's `IsGaloisGroup`.

## To watch for

- Both `M` and `N` must be infinite over `K` and APF.
- The algebra structure of `FieldOfNorms K N` over `FieldOfNorms K M` is not a global instance; statements install it from `FieldOfNorms.inclusion`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Functor/Galois.lean` (SHA-256 of the source file `e359ecf771cccadfa63e585eb96bf3f01172ef9b6a1429ac2365a45771f0f5c1`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
