# The ℤ_p-module structure on principal units

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicPadicModule`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field in the library's sense (`LocalField`) with residue characteristic `p`. The file defines the ℤ_p-module structure on the first principal units `U^1`, written additively. ℤ_p acts coordinatewise on the inverse limit of the quotients `U^1 / U^(n+1)`, and the action is transported to `U^1` and to its adic model. The file then shows that this makes the adic model a topological ℤ_p-module.

## Definitions

- `principalUnitPadicSMul` and `principalUnitPadicModule` (instances): `a • x` is defined by transporting the action on the inverse limit along `principalUnitAddEquivInverseLimitCarrier`, the additive equivalence between `U^1` and the inverse limit (`principalUnitPadic_smul_def`). The module axioms are checked on the inverse limit.
- `adicPrincipalUnitsPadicModule`: the same structure on the wrapper `AdicPrincipalUnits F`, which carries the adic topology. `AdicPrincipalUnits.linearEquivUnderlying` is the resulting ℤ_p-linear equivalence with `U^1`.

## Results

- `Internal.principalUnitPadic_smul_carrier_coordinate`: the level-`n` class of `a • x` is obtained by letting `a` act on the level-`n` class of `x` through the action on the finite quotient (described in the file as reducing `a` modulo `p^(f·n)`).
- `adicPrincipalUnitsHomeomorphProdiscreteLimit_map_smul`, `adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul`: the comparison of the adic model with the prodiscrete inverse limit respects the action. `adicPrincipalUnitsLinearEquivProdiscreteLimit` is its ℤ_p-linear form, and `adicPrincipalUnitsCoordinateLinear F n` the ℤ_p-linear projection to the `n`-th quotient.
- `continuous_adicPrincipalUnitsPadic_smul`, with instances `ContinuousSMul` and `ContinuousAdd` on `AdicPrincipalUnits F`: scalar multiplication and addition are continuous. Both are transported from the prodiscrete limit through the homeomorphism of the two models.

## Watch for

- The action is the library's own construction by transport from the inverse limit, not defined through limits of integer powers; that natural numbers act by powers is not proved in this file.
- Continuity is stated for the wrapper type `AdicPrincipalUnits F`, not for an instance on `U^1` itself.
- `p` is `F.residueCharacteristic`, and every declaration assumes that `F` is a `LocalField` (finite residue field), not merely complete discretely valued.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitPadicAction/AdicPadicModule.lean`: the Lean file is the source byte for byte (SHA-256 `ec9e802c3f7853d82bb546e833ad26d828de10c5bf51bc19636cf3569e4fea21`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
