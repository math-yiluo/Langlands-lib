# The Galois group of the separable closure, acting on the relative field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.Ambient`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, let `Ω` be a separable closure of `K`, and let `L` be an intermediate field of `Ω/K` that is APF and infinite over `K`. Write `X = FieldOfNorms K L` and `U = RelFieldOfNorms K L Ω`, with base embedding `ι = RelFieldOfNorms.baseHom K L Ω : X → U`. For `L/K` normal, the file identifies the Galois group of `Ω/K` with the group of ring automorphisms of `U` whose restriction to `X` comes from an automorphism of `L/K`. The file presents this as Wintenberger's Remark 3.2.4.

## Definitions

- `RelFieldOfNorms.galoisSubgroup K L`: the subgroup of `RingAut U` of those `β` for which some `σ` in `L ≃ₐ[K] L` satisfies `β (ι x) = ι (FieldOfNorms.aut K L σ x)` for all `x`.
- `RelFieldOfNorms.galoisRestrictionFun`, `RelFieldOfNorms.galoisRestriction`: the map sending `β` to that `σ`, as a function and as a group homomorphism to `L ≃ₐ[K] L`.
- `RelFieldOfNorms.galoisRelativeHom`, `RelFieldOfNorms.galoisRelativeKernelEquiv`: the map from `U ≃ₐ[X] U` into the subgroup, and its isomorphism with the kernel of `galoisRestriction`.
- `RelFieldOfNorms.galoisKernelEquiv`: the isomorphism of `Ω ≃ₐ[L] Ω` with that kernel, through `RelFieldOfNorms.autEquiv`.
- `RelFieldOfNorms.ambientGaloisHom` (for `L/K` normal): the action `RelFieldOfNorms.absoluteAut K L` of `Ω ≃ₐ[K] Ω`, with values in the subgroup.
- `RelFieldOfNorms.ambientGaloisEquiv` (for `L/K` normal): the group isomorphism `(Ω ≃ₐ[K] Ω) ≃* galoisSubgroup K L`.

## Results

- `mem_galoisSubgroup_iff_stable_image`: membership means that `β` preserves the image of `ι` and induces there a map in the image of `FieldOfNorms.aut K L`.
- `galoisSubgroup_base_unique`: the automorphism `σ` in the square is unique.
- `galoisRestriction_eq_iff`, `mem_galoisRestriction_ker_iff`: the restriction is characterized by the square; its kernel consists of the automorphisms fixing the image of `ι` pointwise.
- `ambientGaloisHom_restriction`: the restriction of the image of `σ` is `AlgEquiv.restrictNormalHom L σ`.
- `ambientGaloisHom_injective`, `ambientGaloisHom_surjective`; `ambientGaloisEquiv_apply`: the isomorphism acts on `U` as `RelFieldOfNorms.absoluteAut`.

## Proofs

Uniqueness of `σ` is faithfulness of the action on `X` (`FieldOfNorms.aut_injective`). The kernel statement uses `RelFieldOfNorms.autEquiv`, which identifies `Ω ≃ₐ[L] Ω` with `U ≃ₐ[X] U`. Bijectivity of the ambient homomorphism follows by comparison: restriction to `L` is surjective with kernel `Ω ≃ₐ[L] Ω`, and `galoisRestriction` has kernel identified with the same group.

## To watch for

- The result is an isomorphism of abstract groups; no topology is put on `galoisSubgroup` here.
- The subgroup, the restriction and the kernel isomorphisms do not need `L/K` normal; the ambient homomorphism and the final isomorphism do.
- That `U` is a separable closure of `X`, as the header says, is not proved in this file.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3; Remark 3.2.4.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/Ambient.lean` (SHA-256 of the source file `37cd69ad5f2fd1a9402a350163c70435b60c620081a2d89d743ca5b7336927dd`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
