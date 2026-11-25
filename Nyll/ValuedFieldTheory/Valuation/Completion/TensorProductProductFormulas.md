# Degree, norm and trace through a product decomposition of A ⊗_K L

Module `Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductProductFormulas`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Abstract linear algebra: given a finite extension `L / K`, a field `A` over `K`, and an `A`-algebra isomorphism `e : A ⊗_K L ≃ ∏ᵢ Bᵢ` onto a finite product of fields finite over `A`, the degree, norm and trace of `L / K` split over the factors.

## Main results

- `baseChange_pi_finrank_eq_sum`: `[L : K] = ∑ᵢ [Bᵢ : A]`.
- `baseChange_pi_norm_eq_prod`: for `x ∈ L`, the image in `A` of `Algebra.norm K x` is `∏ᵢ Algebra.norm A (e(1 ⊗ x)ᵢ)`.
- `baseChange_pi_trace_eq_sum`: the image in `A` of `Algebra.trace K L x` is `∑ᵢ Algebra.trace A Bᵢ (e(1 ⊗ x)ᵢ)`.

## Proof

Norm, trace and rank are unchanged by base change to `A`, are preserved by algebra isomorphisms, and are multiplicative, respectively additive, on finite products (the product formulas of the library).

## Points to watch

The factors are the components of the given isomorphism `e`, not images of `x` in completions `L_w`. Identifying them with the canonical maps into `L_w` is not done here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/TensorProductProductFormulas.lean`: the Lean file is the source byte for byte (SHA-256 `c114e12488cbec018f4b8c0d2c7178d56a20ecc2e440534f96c0c3a97ba6b663`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
