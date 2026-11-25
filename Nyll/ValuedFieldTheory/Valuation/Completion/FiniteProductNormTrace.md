# Norm and trace on a finite product of algebras

Module `Nyll.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Linear algebra for finite products of algebras with possibly different ranks: the norm of an element of `∏ᵢ Aᵢ` is the product of the norms of its components, and its trace is the sum of their traces. These are the product formulas needed when a tensor product `K_v ⊗_K L` splits into local factors.

## Main results

- `algebra_norm_pi_apply`: for a commutative ring `R`, a finite index type `ι` and commutative `R`-algebras `Aᵢ` that are free and finite as `R`-modules, `Algebra.norm R x = ∏ᵢ Algebra.norm R (x i)` for `x : ∀ i, Aᵢ`.
- `algebra_trace_pi_apply`: under the same hypotheses, `Algebra.trace R (∀ i, Aᵢ) x = ∑ᵢ Algebra.trace R Aᵢ (x i)`.
- `algebra_norm_prod_apply`: the binary case of the norm formula, from `algebra_lmul_prod_eq_prodMap` (multiplication on `S × T` is the product of the two multiplication maps) and Mathlib's determinant of a product map.

Auxiliary items: `moduleFiniteOfPi` (if a product of `R`-modules is finitely generated, so is each factor), and the algebra equivalences `piCongrLeftAlgEquiv` (reindexing a dependent product) and `piOptionEquivProdAlgEquiv` (splitting off the `none` coordinate of an `Option`-indexed product).

## Proof

Induction on the finite index type (empty type, adding one point via `Option`, transport along an equivalence), using the binary norm formula above and Mathlib's binary trace formula.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/FiniteProductNormTrace.lean`: the Lean file is the source byte for byte (SHA-256 `c024b5b7746f9eb3703a95bffd6eb83bd1fe49b3db8a26de7e9e0d6692c8de0f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
