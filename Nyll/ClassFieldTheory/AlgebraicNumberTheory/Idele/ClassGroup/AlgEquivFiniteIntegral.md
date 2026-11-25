# Local integers under the transport of completions

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivFiniteIntegral`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For number fields K and M with a ℚ-algebra isomorphism e : K ≃ M, and a finite place W of M with corresponding place w of K, the library has a map `finitePlaceAdicCompletionCongrHom e W` from the adic completion of K at w to that of M at W.

- `finitePlaceAdicCompletionCongrHom_mapsToIntegers`: this map carries the valuation ring of the completion at w into the valuation ring of the completion at W.

The map raises valuations to the power of the ramification index of W over w, which is nonzero, so elements of valuation at most 1 keep valuation at most 1. This is the compatibility with integers that the restricted-product description of adelic transport needs.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquivFiniteIntegral.lean`: the Lean file is the source byte for byte (SHA-256 `cda5809a4dd197dba55b8d5e5ef2ce8ec6c46bf2e6969280118cdac331e4ef52`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
