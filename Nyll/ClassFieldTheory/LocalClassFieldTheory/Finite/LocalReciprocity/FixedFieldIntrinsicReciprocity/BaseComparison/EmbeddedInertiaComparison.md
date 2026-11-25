# Inertia of an embedded extension: intrinsic and ambient

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedInertiaComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ F ⊆ E` with `K`, `F` nonarchimedean local fields, `F/K` finite separable with compatible valuations, and `E/F` finite Galois. Fix a `K`-embedding `j : E →ₐ[K] K^sep` and an `F`-isomorphism `e` from the separable closure of `F` to `K^sep`. Let `H₀` and `J₀` be the subgroups of `Gal(K^sep/K)` fixing the images of `F` and `E`. The isomorphism `ψ = intrinsicBaseEquivAmbientEmbeddedField` from `Gal(F^sep/F)` onto `H₀`, induced by `e`, carries the inertia of `E/F` computed over `F` to the inertia computed inside `Gal(K^sep/K)`.

## Main results

- `intrinsicExtensionInertia_iff_ambientEmbeddedField`: for `τ ∈ Gal(F^sep/F)`, `τ` lies in the extension inertia of the intrinsic presentation of `E/F`, taken for `localResidueDatum F`, if and only if `ψ(τ)` lies in the extension inertia of `J₀ ≤ H₀`, taken for `localResidueDatum K`.
- `map_intrinsicExtensionInertia_eq_ambientEmbeddedField`: `ψ` maps the first subgroup onto the second.

## Proof

Extension inertia is the intersection of the extension subgroup with the field inertia, and field inertia is the kernel of the normalized degree (`normalizedDegree_ker`). The extension-subgroup part is `intrinsicExtensionSubgroup_iff_ambientEmbeddedField`. For the inertia part, the normalized degrees of `τ` over `F` and of `ψ(τ)` over the ambient fixed field agree (`intrinsicBase_normalizedDegree_eq_ambientEmbeddedField`).

## Points to watch

- "Inertia" here is the library's `extensionInertiaWithin` for a residue datum, defined through the normalized degree. It is not Mathlib's inertia subgroup of a prime ideal.
- The fields live in `Type`, and the comparison depends on the chosen `j` and `e`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedInertiaComparison.lean`: the Lean file is the source byte for byte (SHA-256 `73c5a24c67b9cf4947dfd18adfd3aa895e3caa736308112075d5323e5aace135`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
