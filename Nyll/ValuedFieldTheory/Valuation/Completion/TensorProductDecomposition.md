# The decomposition L ⊗_K K_v ≃ ∏_w L_w over the extensions w of v

Module `Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite separable extension `L / K` and a nontrivial real absolute value `v` on `K`, the canonical map from `L ⊗_K K_v` to the product of the completions `L_w` over the absolute values `w` on `L` extending `v` is an isomorphism of `K_v`-algebras. The file also shows that there are finitely many such `w`.

## Main definitions and results

- `completionTensorDecomposition_powerBasis`: the power basis of `L / K` given by a primitive element.
- `completionTensorDecomposition_extensionFintype`: a `Fintype` instance on `AbsoluteValueExtension vK L`, obtained from the library's bijection between extensions `w` and the distinct irreducible factors over `K_v` of the minimal polynomial of the primitive element.
- `completionTensorDecomposition_mapped_minpoly_eq_prod_extensionFactors`: that minimal polynomial, mapped to `K_v[X]`, is the product over `w` of the factor attached to `w`; `completionTensorDecomposition_extensionFactors_pairwise_coprime`: factors for different `w` are coprime.
- `completionTensorDecomposition_factorEquiv`: the isomorphism `K_v ⊗_K L ≃ ∏_w L_w` built from these factors; `completionTensorDecomposition_factorEquiv_toAlgHom`: its underlying map is the canonical product map `completionTensorMap_leftCanonicalHom`.
- `completionTensorDecomposition_left`: the isomorphism `K_v ⊗_K L ≃ ∏_w L_w` defined directly as the canonical map, with `b ⊗ a ↦ (b·a)_w`.
- `completionTensorDecomposition`: the same in the order `L ⊗_K K_v`, sending `a ⊗ b` to `(a·b)_w`; `completionTensorDecomposition_toAlgHom` records that it is the canonical map.
- `localTensorUnitsEquivCompletionProduct`: the induced isomorphism of unit groups `(K_v ⊗_K L)ˣ ≃ ∏_w L_wˣ`.

## Proof

Write `L = K(α)`. Then `K_v ⊗_K L` is `K_v[X] ⧸ (f)` with `f` the minimal polynomial of `α` mapped to `K_v`. Being separable and monic, `f` is the product of its distinct irreducible factors, which are pairwise coprime, so the Chinese remainder theorem splits the algebra into the algebras obtained by adjoining a root of each factor. Each of these is identified with the corresponding `L_w` by the extension-factor correspondence proved elsewhere in the library. The composite sends `1 ⊗ α` to the image of `α` in each `L_w`, so it agrees with the canonical map on a power basis, hence everywhere.

## Points to watch

- The index set is the type of real absolute values on `L` extending `v` exactly, not a set of places up to equivalence.
- Separability of `L / K` is a hypothesis of every result; nontriviality of `v` is a hypothesis of all but `completionTensorDecomposition_powerBasis`, which involves no absolute value.
- The two tensor orders `K_v ⊗_K L` and `L ⊗_K K_v` are both provided; the second uses the right-algebra structure `Algebra.TensorProduct.rightAlgebra`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/TensorProductDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `514bd6f754b0b78b05436f2cc2f585c1bc346bb885cf4219813670f52635ad90`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
