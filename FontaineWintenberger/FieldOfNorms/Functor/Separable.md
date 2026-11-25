# Finite separable extensions of the field of norms

Module `FontaineWintenberger.FieldOfNorms.Functor.Separable`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, and let `M ⊆ N` be infinite separable APF extensions of `K` with `N/M` finite. The file shows that `FieldOfNorms K N` is a finite separable extension of `FieldOfNorms K M`, through `FieldOfNorms.inclusion`, of degree `[N : M]`, with no normality assumption. It then transports these facts, and the Galois statements, to the map `FieldOfNorms.map τ` attached to an arbitrary `K`-embedding `τ`.

## Results for an inclusion

- `FieldOfNorms.inclusion_isScalarTower`: for a tower `M ⊆ N ⊆ P` of finite separable steps, the three inclusions of fields of norms form a scalar tower.
- `FieldOfNorms.finiteDimensional_isSeparable_finrank_inclusion`: the extension `FieldOfNorms K N` over `FieldOfNorms K M` is finite-dimensional, separable, and of degree `Module.finrank M N`.
- `FieldOfNorms.finiteDimensional`, `FieldOfNorms.isSeparable`, `FieldOfNorms.finrank`: the three parts.

## Results for an embedding

Here `τ : L →ₐ[K] M` is a `K`-embedding with `M` finite over the image `τ.fieldRange`, and `FieldOfNorms K M` is an algebra over `FieldOfNorms K L` through `FieldOfNorms.map τ`.

- `FieldOfNorms.finiteDimensional_isSeparable_finrank_map`: if `M` is separable over the image, the extension of fields of norms is finite-dimensional, separable, of degree `Module.finrank τ.fieldRange M`.
- `FieldOfNorms.isGalois_map`: if `M` is Galois over the image, the extension of fields of norms is Galois.
- `FieldOfNorms.autEquivOfMap`: in that case, the group isomorphism from `M ≃ₐ[τ.fieldRange] M` to the automorphism group of `FieldOfNorms K M` over `FieldOfNorms K L`; `autEquivOfMap_apply`: it sends `σ` to `FieldOfNorms.mapEquiv` of `σ` viewed over `K`.

## Proofs

For an inclusion, let `P` be the normal closure of `N/M` inside an algebraic closure of `N`. Then `P` is finite Galois over both `M` and `N`, and it is again APF and infinite over `K` (`isAPF_finite_extension_iff`). By the file on Galois actions, `FieldOfNorms K P` is finite Galois over `FieldOfNorms K M` and over `FieldOfNorms K N`, of degrees `[P : M]` and `[P : N]`. Finiteness and separability of the bottom step follow from the tower, and the degree from multiplicativity of degrees. For an embedding, `FieldOfNorms.map τ` is the inclusion for `τ.fieldRange ⊆ M` composed with the isomorphism `FieldOfNorms.mapEquiv τ.equivFieldRange`, and each property is transported along that isomorphism.

## To watch for

- Separability of `N/M` is not an extra hypothesis for the inclusion results: it is derived from separability of `N` over `K`.
- Both fields must be infinite over `K` (`Fact (¬ Module.Finite K _)`) and APF.
- The algebra structures on fields of norms are installed inside each statement (`(FieldOfNorms.inclusion K M N).toAlgebra`, `(FieldOfNorms.map τ).toAlgebra`); they are not global instances.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Functor/Separable.lean` (SHA-256 of the source file `e6254125543e2e93599dc0638049fd825409edcf012130af746d43db8d5d70bc`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
