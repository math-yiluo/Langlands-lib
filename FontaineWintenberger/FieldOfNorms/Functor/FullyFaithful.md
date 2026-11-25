# Full faithfulness of the field of norms on finite separable extensions

Module `FontaineWintenberger.FieldOfNorms.Functor.FullyFaithful`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, and let `L/K` be an infinite separable APF extension. For finite extensions `M`, `N` of `L` that are separable over `K`, the file shows that `L`-embeddings `M → N` correspond bijectively to embeddings of the fields of norms over `FieldOfNorms K L`. The file presents this as the finite case of Wintenberger's Theorem 3.2.2 (ii).

## Definitions

- `FieldOfNorms.mapAlgHom K L M N φ`: for `φ : M →ₐ[L] N`, the homomorphism `FieldOfNorms K M → FieldOfNorms K N` of `FieldOfNorms K L`-algebras, given by `FieldOfNorms.map` of `φ` viewed as a `K`-embedding. The algebra structures come from `FieldOfNorms.inclusion`.
- `FieldOfNorms.algHomEquiv`: the bijection `(M →ₐ[L] N) ≃ (FieldOfNorms K M →ₐ[FieldOfNorms K L] FieldOfNorms K N)`, built from `mapAlgHom`.

## Results

- `FieldOfNorms.mapAlgHom_bijective`: `mapAlgHom` is bijective, with no normality assumption on `M` or `N`.
- `FieldOfNorms.mapAlgHom_comp`, `mapAlgHom_algebraMap`, `mapAlgHom_postcomp_aut`: `mapAlgHom` respects composition, sends an inclusion `M ⊆ N` to `FieldOfNorms.inclusion K M N`, and turns composition with an automorphism `σ` of `N/L` into `FieldOfNorms.mapEquiv σ`.
- `FieldOfNorms.mapEquiv_fixes_inclusion_iff`, `mapEquiv_eq_on_inclusion_iff`: for `N/L` finite Galois and `M` between them, an automorphism `σ` of `N/L` acts trivially on the image of `FieldOfNorms K M` exactly when it fixes `M`; two automorphisms agree there exactly when they agree on `M`.
- `FieldOfNorms.mapAlgHom_bijective_of_isGalois`: the case where `N/L` is Galois and contains `M`.
- `FieldOfNorms.mapAlgHom_injective_of_isGalois_top`, `mapAlgHom_surjective_of_isGalois_top`: the case where `M` and `N` lie in a finite Galois `P/L`.
- Field-theoretic helpers: `exists_algHom_factor_of_fixed` (an embedding into a Galois extension `C/B` whose image is fixed by the Galois group factors through `B`), `exists_common_finiteGalois_embeddings` (two finite separable extensions embed in one finite Galois subfield of a separable closure).

## Proof

In the Galois case, an embedding `φ` is extended to an automorphism of `N/L`; the isomorphism `FieldOfNorms.autEquiv` between the Galois groups of `N/L` (or `N/M`) and of the fields of norms gives injectivity and surjectivity. Surjectivity also uses that `FieldOfNorms K N` is Galois over `FieldOfNorms K L` (`FieldOfNorms.isGalois`). In general, `M` and `N` are embedded in a common finite Galois `P/L`; a homomorphism of fields of norms is lifted to an embedding `M → P`, shown to be fixed by the Galois group of `P/N`, and factored through `N`.

## To watch for

- The statement covers finite extensions of `L` only, not arbitrary algebraic separable ones.
- `L/K` must be infinite (`Fact (¬ Module.Finite K L)`); the intermediate theorems also take APF and infiniteness of `M`, `N`, `P` as instances, while `algHomEquiv` derives them from `L`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3; Theorem 3.2.2 (ii).

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Functor/FullyFaithful.lean` (SHA-256 of the source file `6488f0c8725395feaf522a0306d52f1f739aa69f8a39b04b64b18793604e3d44`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
