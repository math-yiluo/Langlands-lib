# Explicit unramified local reciprocity

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite unramified Galois extension L/K of nonarchimedean local fields, the file builds the reciprocity isomorphism explicitly: the norm quotient K^×/N(L^×) is identified with ℤ/nℤ, n = [L:K], through the valuation, and ℤ/nℤ with the cyclic group Gal(L/K) through arithmetic Frobenius. The Artin map obtained this way sends x to Frob^(`valuationMap` x).

## Main definitions and results

Hypotheses throughout: K : Type u and L : Type v nonarchimedean local fields, L/K finite Galois, the valuation of L extending that of K, `IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, `IsUnramifiedValuedExtension K L`.

- `unramifiedLocalReciprocityIsoToGaloisGroup : NormQuotient K L ≃* Gal(L/K)`: the valuation isomorphism `normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure` followed by the inverse of the Frobenius-normalized `galoisGroupEquivZModOfUnramifiedValuationNormalized`.
- `unramifiedLocalReciprocityIso : NormQuotient K L ≃* Abelianization (Gal(L/K))`: the same followed by the identification of the cyclic group with its abelianization.
- `unramifiedLocalArtinMap : Kˣ →* Abelianization (Gal(L/K))`, the composite with the quotient map (`unramifiedLocalArtinMap_apply`).
- Evaluation lemmas: the class of `inverseIntegerRingUniformizerFieldUnit K` goes to arithmetic Frobenius (`..._inverseIntegerRingUniformizerFieldUnit`, with `_zpow` forms), and the class of any x goes to Frob^(`valuationMap` x) (`unramifiedLocalReciprocityIsoToGaloisGroup_normClass`, `unramifiedLocalReciprocityIso_normClass`, `unramifiedLocalArtinMap_eq_frobenius_zpow`).

## Caveats

- The element sent to Frobenius is the inverse of a chosen uniformizer, which has `valuationMap` equal to 1. So the exponent `valuationMap K x` is minus the usual order of x, and a uniformizer goes to the inverse of arithmetic Frobenius.
- This is the explicit, Frobenius-normalized isomorphism; its agreement with the canonical class-formation reciprocity map is not proved in this file. The docstrings note that the norm-subgroup equality and the normalization are proved internally, not taken as hypotheses.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `d5af1ec5098c5dc5f7e05241bd49108abc162c7810c071cbf6951226c0ca6a80`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
