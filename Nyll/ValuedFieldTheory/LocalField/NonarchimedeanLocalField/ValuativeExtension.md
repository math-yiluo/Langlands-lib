# Valuative extensions of valued fields

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an extension `L / K` of fields with valuative relations, the file introduces the condition that the valuation ring of `L` is integral over that of `K`, which the library uses to restrict field norms to valuation rings. It also shows that nontriviality of a valuation passes to an extension.

- `Valuation.IsNontrivial.of_hasExtension`: if `vR` on a commutative ring `R` is nontrivial and `vA` on an `R`-algebra `A` extends it (`vR.HasExtension vA`), then `vA` is nontrivial; an element of value neither 0 nor 1 keeps that property.
- `ValuativeExtension K L`: a `Prop` class saying every element of `𝒪[L]` is integral over `𝒪[K]`.
- `valuativeExtensionOfIsIntegralClosure`: an instance, when `𝒪[L]` is the integral closure of `𝒪[K]` in `L`.

## Watch for

`LocalFieldTheory.ValuativeExtension` is the library's own class. Despite its name it does not ask the relation on `L` to restrict to the relation on `K`; it records only integrality of `𝒪[L]` over `𝒪[K]`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuativeExtension.lean`: the Lean file is the source byte for byte (SHA-256 `69f1ff828f1a5beb67a4034273d8b2c0ed2bd73454a2ca30493be1502fb24793`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
