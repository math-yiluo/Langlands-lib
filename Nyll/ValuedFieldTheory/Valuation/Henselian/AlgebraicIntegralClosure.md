# The integral closure of a Henselian valuation ring is a valuation ring

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicIntegralClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `V` be a valuation subring of a field `K`, Henselian along its maximal ideal, and `L/K` an algebraic extension.

`integralClosure_mem_or_inv_of_henselianRing`: for every `z : L`, either `z` or `z⁻¹` is integral over `V`; that is, the integral closure of `V` in `L` satisfies the valuation-ring dichotomy. There is no restriction on rank, value group, completeness or separability.

## Proof

Embed `L` into an algebraic closure `Ω` of `K` and extend the valuation of `V` to a valuation subring `B` of `Ω` by Chevalley's theorem; then `ι(z)` or its inverse lies in `B`. For `α ∈ B`, all roots in `Ω` of the minimal polynomial of `α` over `K` have the same `B`-value as `α`, by a consequence of Henselianity proved in an imported file (lifting of monic coprime factorizations over the residue field). The nonarchimedean bound on coefficients of `∏ (X − βᵢ)` then puts every coefficient of the minimal polynomial in `V`, so `α` is integral over `V`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/AlgebraicIntegralClosure.lean`: the Lean file is the source byte for byte (SHA-256 `7d8f1b8aca2c8485ca9965503f22537c2d4f75dae0ee0b65977c8ae14a8bbd8e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
