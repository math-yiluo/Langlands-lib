# Norm and trace under scalar extension

Module `Nyll.ValuedFieldTheory.Valuation.Completion.BaseChangeNormTrace`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `A/K` and a commutative `K`-algebra `L` that is free and finite as a `K`-module, the norm and the trace of `1 ⊗ x` in `A ⊗_K L` over `A` are the images in `A` of the norm and trace of `x` in `L` over `K`. These are the comparisons used when passing from `L/K` to its scalar extension to a completion `K_v`.

## Main results

- `algebra_norm_baseChange_tmul`: the norm of `1 ⊗ x` over `A` is the image in `A` of the norm of `x` over `K`.
- `algebra_trace_baseChange_tmul`: the trace of `1 ⊗ x` over `A` is the image in `A` of the trace of `x` over `K`.

## Proof

Multiplication by `1 ⊗ x` is the base change of multiplication by `x`, and determinant and trace of linear maps commute with base change (Mathlib's `LinearMap.det_baseChange` and `LinearMap.trace_baseChange`).

## Points to watch

- `K` and `A` must be fields; `L` need only be a commutative ring, free and finite over `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/BaseChangeNormTrace.lean`: the Lean file is the source byte for byte (SHA-256 `9ee8d13a632c062c9885a9cc5c30a6fa7f8ae6e6e11f656df1d9a423cdbaed5a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
