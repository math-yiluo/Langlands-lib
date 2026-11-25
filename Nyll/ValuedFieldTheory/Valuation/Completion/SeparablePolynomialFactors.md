# A separable polynomial is the product of its distinct irreducible factors

Module `Nyll.ValuedFieldTheory.Valuation.Completion.SeparablePolynomialFactors`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Two factorization facts used in the Chinese remainder proof of the tensor product decomposition `K_v ⊗_K L ≃ ∏_w L_w`.

## Main results

- `separable_monic_eq_prod_distinctNormalizedFactors`: a monic separable polynomial `p` over a field equals the product of its distinct monic irreducible factors (the type `DistinctNormalizedFactors p` of the library). Separability makes `p` squarefree, so its multiset of normalized factors has no repetitions.
- `distinctNormalizedFactors_pairwise_coprime`: two different factors from `DistinctNormalizedFactors p` are coprime. This holds for any polynomial `p`, separable or not.

## Points to watch

The product formula needs `p` monic as well as separable; without monicity it holds only up to the leading coefficient.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Completion/SeparablePolynomialFactors.lean`: the Lean file is the source byte for byte (SHA-256 `0eff2f0bad8b1a6eb8e69194fe119936085be4e82497d9d33c8d45412e1d956e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
