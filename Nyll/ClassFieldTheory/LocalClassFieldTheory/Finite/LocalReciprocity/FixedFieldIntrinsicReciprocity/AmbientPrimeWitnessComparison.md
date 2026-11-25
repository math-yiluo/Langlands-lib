# The prime witness under the local Artin map and the ambient symbol

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitnessComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ F ⊆ E` with `K`, `F` nonarchimedean local fields, `F/K` finite separable with compatible valuations, `E/F` finite abelian, a `K`-embedding `j : E →ₐ[K] K^sep` and an `F`-isomorphism `e` from the separable closure of `F` to `K^sep`. For `z ∈ Gal(E/F)^ab`, let `x` be the prime witness `ambientEmbeddedPrimeWitness K F E j e z`, the norm to `F` of a chosen valuation-one unit of a Frobenius fixed field. The file proves that both the local Artin map of `E/F` and the ambient fixed-field norm-residue construction send `x` to `z`.

## Main results

- `ambientEmbeddedPrimeWitness_local`: `localArtinMonoidHom F E x = z`.
- `ambientEmbeddedPrimeWitness_symbol`: proves `ambientEmbeddedPrimeSymbolProperty K F E j e z`. This is the formula that the ambient symbol of the witness is the abelianized ambient Frobenius restriction.
- `ambientEmbeddedPrimeTransportValue_eq_target`: the transported ambient value of the witness equals `ambientEmbeddedPrimeTarget K F E j e z`. This removes the hypothesis of `ambientEmbeddedPrimeTransportValue_eq_target_of_symbol`.
- `ambientEmbeddedPrimeTarget_eq`: the target equals `z`.
- `ambientEmbeddedPrimeWitness_ambient`: `ambientEmbeddedNormResidueAbelianElement K F E j e x = z`.

## Proofs

For the local statement, the chosen unit of the Frobenius fixed field `L_F` over `F` has valuation one. So it is a prime element for `localHenselianValuation F` (`localHenselianValuation_isPrimeElement_abstractFixedField`), and its abstract relative norm is its field norm. The concrete norm-residue symbol on such a prime norm is the abelianized Frobenius restriction (`concreteNormResidueSymbolOfEmbedding_apply_primeNorm`). The local Artin map equals the concrete symbol for the embedding of `E` into the separable closure of `F` (`localArtinMonoidHom_eq_of_embedding`).

For the ambient statement, the image of the unit in the ambient Frobenius fixed field `L_H` also has valuation one, hence is a prime element for `localHenselianValuation K`. With the compatibility of `L_F ≅ L_H` with `F` and its ambient fixed field, `abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit` gives the symbol formula. The target equals `z` because Frobenius restriction commutes with the transport of Frobenius elements (`intrinsicFrobeniusRestriction_compatibility_ambientEmbeddedField`).

## Points to watch

- The statements are about the chosen witnesses: for each `z` they give one unit on which both maps take the value `z`, not a comparison of the two maps at every unit.
- The fields live in `Type`, and the results depend on the chosen `j` and `e`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeWitnessComparison.lean`: the Lean file is the source byte for byte (SHA-256 `de23b75dd4376433821a8bf2846fed332a854b0caf77e489507de7f9932b8f09`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
