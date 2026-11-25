# Complete discrete valuations on local fields and their finite extensions

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file connects Mathlib's nonarchimedean local fields (`IsNonarchimedeanLocalField`, built on `ValuativeRel`) with the library's structure `CompleteDVF` of complete discretely valued fields, and equips every finite separable extension of a local field with a complete discrete valuation extending the base one.

## Definitions and results

- `localCompleteDVF K`: the canonical valuation of a nonarchimedean local field `K` as a `CompleteDVF K`. Rank-one discreteness comes from Mathlib's identification of the value group with `ℤᵐ⁰`.
- `localCompleteDVFValuation_hasExtension`: if both `K` and `L` are local fields and the valuation of `L` extends that of `K`, the same holds for their `localCompleteDVF` valuations.
- `localCompleteDVF_integerRing_isIntegralClosure` and `localCompleteDVF_integerRing_moduleFinite`: for a finite separable extension `L/K` of local fields with extending valuations, `𝒪[L]` is the integral closure of `𝒪[K]` in `L` and a finite `𝒪[K]`-module.
- `chosenLocalExtensionCompleteDVF_exists`: for any finite separable extension `L` of a local field `K`, there is a `CompleteDVF L` whose valuation extends that of `K` and whose valuation ring is the integral closure of `𝒪[K]`.
- `chosenLocalExtensionCompleteDVF K L`: such a structure, chosen. It comes with the extension property (also an instance), the integral-closure property, finiteness of the valuation ring as a module, and `chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension`, the uniqueness of the extended valuation in the library's sense.

## Proofs

`localCompleteDVF` is built from Mathlib's valued-field structure through a library constructor for complete valued fields. The existence statement comes from the library result `exists_integralClosure_standard_fundamental_identity`; its further conclusion, a defectlessness statement, is dropped here. Uniqueness comes from a library result for finite separable extensions of complete DVFs.

## Watch for

- `chosenLocalExtensionCompleteDVF` is chosen by `Classical.choose`. `L` need not carry a local-field structure, and nothing ties the chosen valuation to one when it does.
- The chosen structure has value group in universe `0`, while `localCompleteDVF K` has value group in the universe of `K`.
- All extension results except `localCompleteDVFValuation_hasExtension` assume `L/K` finite and separable.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`: the Lean file is the source byte for byte (SHA-256 `d3fa8b4a675e61267cb02b974aab687a10c60275b9a506ea60230c8af3f07bd5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
