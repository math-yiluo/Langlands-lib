# Structure of the unit group of a local field

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file assembles the structure theorem for `Kˣ`, where `K` is a local field given by a complete discrete valuation `v : K → ℤᵐ⁰` with finite residue field of order `q` and residue characteristic `p`. It combines the valuation factor `ℤ`, the Teichmüller factor `ℤ/(q−1)` and a description of the first principal units `U¹` into isomorphisms of topological groups, for the topology of `Valued.mk' v`. The factors are ordered: uniformizer, roots of unity, principal units.

## Main definitions

- `chosenFieldUnitsStructure_mixedCharacteristic`: for `CharZero K` and `v` surjective, a natural number `a` together with `ℤ × (ℤ/(q−1) × (ℤ/p^a × ℤ_p^d)) ≃ₜ* Kˣ`, where `d = [K : ℚ_p]`. The description of `U¹` as `ℤ/p^a × ℤ_p^d` is `chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation`, from the imported mixed-characteristic files.
- `chosenFirstPrincipalUnitStructure_equalCharacteristic`: for `CharP K p`, `∏_ℕ ℤ_p ≃ₜ* U¹`. It composes the Iwasawa description of `U¹` as a product of copies of `ℤ_p`, indexed by degrees prime to `p` and residue-field basis coordinates (`iwasawaGlobalAdicPrincipalUnitsContinuousAddEquiv`), with a reindexing of that product by `ℕ`.
- `chosenFieldUnitsStructure_equalCharacteristic`: for `CharP K p`, `ℤ × (ℤ/(q−1) × ∏_ℕ ℤ_p) ≃ₜ* Kˣ`.

The two descriptions of `Kˣ` are obtained by feeding the description of `U¹` into the assembly map `fieldUnitsContinuousMulEquivUniformizerRootsPrincipalUnitsOfWithZeroValuation`, with a uniformizer chosen by `Classical.choose`.

## Points to watch

- The isomorphisms are not canonical: they depend on a chosen uniformizer; the mixed one also on the description of `U¹` supplied by `chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation`, and the equal-characteristic ones on the Iwasawa generators and on a chosen bijection of the Iwasawa index set with `ℕ`.
- In the mixed case the exponent `a` is only produced as part of a dependent pair; the file does not identify it, for instance with the `p`-power roots of unity in `K`.
- The mixed case requires `v` to be surjective, and `d` is `Module.finrank ℚ_p K` for the `ℚ_p`-algebra structure given by `mixedWithZeroValuationContext v`.
- In equal characteristic the hypothesis is `CharP K p` with `p` the residue characteristic of `ofWithZeroValuation v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/FieldUnitStructure.lean`: the Lean file is the source byte for byte (SHA-256 `57b17e55b72a5019389f7e1993a8b2ed5f1c2f911e7930ca37abe124fae6bf30`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
