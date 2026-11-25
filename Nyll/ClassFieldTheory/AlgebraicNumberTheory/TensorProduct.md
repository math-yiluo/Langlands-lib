# Coprime base change of a finite Galois extension

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

If `M/K` and `L/K` are finite field extensions of coprime degrees, then `M ⊗[K] L` is a field, and if `L/K` is Galois, `M ⊗[K] L` is Galois over `M`. The module comment says this is the fact used in a descent through roots of unity.

## Main definitions and results

- `tensorProduct_isField_of_finrank_coprime`: for finite-dimensional `M` and `L` over a field `K` with `[M:K]` and `[L:K]` coprime, `M ⊗[K] L` is a field (`IsField`).
- `tensorBaseChangeAut K M L σ`: an automorphism `σ` of `L/K` gives the `M`-algebra automorphism `id_M ⊗ σ` of `M ⊗[K] L`. `tensorBaseChangeAut_tmul` computes it on pure tensors, and `tensorBaseChangeAut_injective` says that `σ ↦ id ⊗ σ` is injective; these two need neither finiteness nor the Galois hypothesis.
- `tensorProduct_isGalois_of_finrank_coprime`: under the same coprimality and with `L/K` Galois, `M ⊗[K] L`, with the field structure given by the first theorem, is Galois over `M`.

## Proofs

For the field statement, `M` and `L` are embedded into an algebraic closure of `K`; their images are linearly disjoint because their degrees are coprime (Mathlib's `IntermediateField.LinearDisjoint.of_finrank_coprime`), and a linearly disjoint pair with one algebraic factor has a tensor product that is a field. For Galoisness, `[M ⊗ L : M] = [L : K]` by base change; the automorphisms `id ⊗ σ` give at least `[L : K]` distinct `M`-automorphisms, the number of automorphisms is always at most the degree, and equality characterizes Galois extensions.

## Points to watch

The field structure on `M ⊗[K] L` in the Galois statement is built inside the statement (`letI`) from the first theorem; it is not a global instance, so applying the result requires this same structure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/TensorProduct.lean`: the Lean file is the source byte for byte (SHA-256 `a2c41a9a09e748fdeb1d006b45e47cac0bb72e03874aed8f291860a89afedf50`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
