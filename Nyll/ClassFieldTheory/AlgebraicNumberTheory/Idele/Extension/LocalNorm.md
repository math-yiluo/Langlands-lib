# The local norm as a product over the places above

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite separable field extension and `vK` a nontrivial absolute value on `K`, with completion `K_v`. Under the canonical decomposition `K_v ⊗_K L ≅ ∏_w L_w` over the extensions `w` of `vK` to `L`, the file proves that the determinant norm on `K_v ⊗_K L` is the product of the field norms of the components.

## Main results

- `RelativeIdeleGroup.localNorm_eq_prod`: for `z ∈ K_v ⊗_K L`, `Algebra.norm K_v z = ∏_w Algebra.norm K_v (z_w)`, where `z_w` is the component of `z` under `completionTensorDecomposition_left`.
- `RelativeIdeleGroup.localNorm_units_eq_prod`: the same for units, the form used for idele components.

The norm is invariant under the algebra isomorphism, and the norm on a finite product of algebras is the product of the norms (`algebra_norm_pi_apply`, imported).

## Points to watch

- The product runs over `AbsoluteValueExtension vK L`. Its finiteness and the `K_v`-algebra structures on the `L_w` are supplied by `let`, and the statement holds for these choices.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/LocalNorm.lean`: the Lean file is the source byte for byte (SHA-256 `4e00eb3db18b0ff981ac27ceb850426be5e09b9b8b25fe14709f1d42f9faec32`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
