# The ambient Galois quotient of an embedded finite Galois extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F/K` be finite separable and `E/F` finite Galois, for arbitrary fields in arbitrary universes. Let `j : E →ₐ[K] K^sep` be a `K`-embedding into the separable closure of `K` and `i` its restriction to `F`. Let `e` be an `F`-algebra isomorphism from the separable closure of `F` to `K^sep`, with `F` acting through `i`. Let `H₀` and `J₀` be the subgroups of `Gal(K^sep/K)` fixing `i(F)` and `j(E)`, so `J₀ ≤ H₀`. The file shows that `J₀` is normal of finite index in `H₀` and identifies `H₀/J₀` with `Gal(E/F)`. It does so by transport along the isomorphism `ψ = intrinsicBaseEquivAmbientEmbeddedField K F i e` from `Gal(F^sep/F)` onto `H₀`, which is induced by `e`.

## Main results

- `intrinsicExtensionSubgroup_iff_ambientEmbeddedField`: an element `τ` of `Gal(F^sep/F)` fixes the image of `E` under the embedding `e⁻¹ ∘ j` if and only if `ψ(τ)` fixes `j(E)`.
- `map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`: `ψ` maps the intrinsic extension subgroup of `E/F` onto the ambient extension subgroup given by `J₀ ≤ H₀`.
- `ambientEmbeddedExtensionSubgroup_normal`: that ambient subgroup is normal in `H₀`.
- `ambientEmbeddedExtensionQuotient_finite`: the quotient `H₀/J₀` is finite.
- `ambientEmbeddedExtensionQuotientEquivGaloisGroup`: an isomorphism `H₀/J₀ ≃* Gal(E/F)`. It is the inverse of the quotient isomorphism induced by `ψ`, followed by the intrinsic identification `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`.
- `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`: on the class of `ψ(τ)` it agrees with the intrinsic identification at the class of `τ`.
- `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply`: for `ρ ∈ H₀` and `x ∈ E`, `j` of the image of the class of `ρ`, applied to `x`, equals `ρ(j x)`. So the isomorphism is restriction of `ρ` to `j(E)`.

## Proofs

Each statement is moved across `ψ` from the intrinsic presentation of `E/F` inside `F^sep`. There normality and finiteness hold by construction, and normality is preserved under the surjection `ψ`.

## Points to watch

- `H₀` and `J₀` do not involve `e`, but the normality and finiteness statements take `e` as an argument, since they are proved through `ψ`.
- `extensionSubgroup` is the library's name for `J₀` viewed as a subgroup of `H₀`, and `H₀/J₀` is the ordinary quotient group; `intrinsicAbstractBase` and the intrinsic presentation of `E/F` belong to the library's class-formation framework.
- No local-field hypotheses are used in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `ed8c983412feb6d4732512e7d9dfddb4fe30cd5c1a08bc87af32f78016a56033`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
