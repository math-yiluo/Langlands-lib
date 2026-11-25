# Units modulo first principal units and residue units

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` with a valuative relation, reduction modulo the maximal ideal maps the units `𝒪[K]ˣ` of the valuation ring onto the units `𝓀[K]ˣ` of the residue field, with kernel the first principal units `U¹`. This file sets up `𝒪[K]ˣ/U¹` and proves the resulting isomorphism `𝒪[K]ˣ/U¹ ≃ 𝓀[K]ˣ` in multiplicative, additive and `ℤ`-module form.

## Main definitions and results

- `ResidueUnits K`: a named copy of `𝓀[K]ˣ`, with its group structure, `residueUnitsConcreteEquiv`, and a finiteness instance when `𝓀[K]` is finite.
- `IntegerUnitsModPrincipalUnits K`: the quotient `𝒪[K]ˣ/U¹`, with class map `integerUnitsModPrincipalUnitsMk`, lifting `integerUnitsModPrincipalUnitsLift`, induction principle, and criteria for a class to be trivial or two classes to agree.
- `integerUnitsToResidueUnits K : 𝒪[K]ˣ →* ResidueUnits K`, reduction of units. `principalUnits_one_eq_ker_integerUnitsToResidueUnits`: its kernel is `U¹`. `integerUnitsToResidueUnits_surjective`: every residue unit lifts. `principalUnits_le_ker_reduction`: every `U^n` with `n ≥ 1` reduces to `1`.
- `integerUnitsModPrincipalUnitsEquivResidueUnits`: the isomorphism `𝒪[K]ˣ/U¹ ≃* 𝓀[K]ˣ`, sending a class to the reduction of a representative; `integerUnitsModPrincipalUnitsAddEquivResidueUnits` is its additive form, and `integerUnitsModPrincipalUnitsIsoResidueUnits` the corresponding isomorphism in `ModuleCat ℤ`.
- `integerUnitsModPrincipalUnits_card_eq_residueUnits_card`: the two groups have the same cardinality.

## Proofs

The isomorphism is the first isomorphism theorem for reduction of units, which is surjective because reduction `𝒪[K] → 𝓀[K]` is a surjective local homomorphism.

## Points to watch

- Only `[Field K] [ValuativeRel K]` is assumed.
- The cardinality statement takes finiteness of both groups as instance arguments, although the equality of `Nat.card` it states does not depend on them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueUnits.lean`: the Lean file is the source byte for byte (SHA-256 `19d962e73fff378a5148dfd886aca7c53fe27d958e32857627d9d634a3a73d04`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
