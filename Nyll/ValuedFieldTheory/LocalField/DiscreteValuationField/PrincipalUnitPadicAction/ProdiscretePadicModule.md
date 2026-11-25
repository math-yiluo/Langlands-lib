# The ℤ_p-module structure on lim U¹/U^(n+1)

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.ProdiscretePadicModule`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field `F` (the library's `LocalField`) with residue characteristic p, the inverse limit of the finite quotients U¹/U^(n+1) of the first principal units, written additively, is made a topological module over ℤ_p by letting ℤ_p act on each coordinate through its reduction modulo p^(f·n), where the residue field has p^f elements.

## Main definitions and results

- `Internal.principalUnitInverseLimitCarrierPadicSMul` and `Internal.principalUnitInverseLimitCarrierPadicModule`: the coordinatewise ℤ_p-action on the group of compatible families, and the module structure it gives (built with `Module.ofMinimalAxioms`). Compatibility of the coordinates rests on ℤ_p-linearity of the transition maps.
- `principalUnitProdiscreteLimitPadicModule`: the same structure transported to the wrapper type `PrincipalUnitProdiscreteLimit`, which carries the prodiscrete topology.
- `PrincipalUnitProdiscreteLimit.coordinate_smul` and `PrincipalUnitProdiscreteLimit.coordinateLinear`: evaluation at level n is a ℤ_p-linear map to `DiscretePrincipalUnitQuotient`.
- `continuous_principalUnitProdiscreteLimitPadic_smul` and the instance `principalUnitProdiscreteLimitContinuousSMul`: the action ℤ_p × limit → limit is jointly continuous; `principalUnitProdiscreteLimitContinuousAdd`: addition is continuous.

## Proofs

Continuity is checked coordinatewise, from continuity of the scalar action on each finite discrete quotient, and transported to the wrapper through its homeomorphism with the limit carrier.

## Points to note

- The ℤ_p-action is constructed on the inverse limit, not on U¹ itself; transport to U¹ goes through the identification U¹ ≅ lim U¹/U^(n+1) of another file.
- The scalar action on each level n factors through ℤ/p^(f·n), where p^f is the size of the residue field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitPadicAction/ProdiscretePadicModule.lean`: the Lean file is the source byte for byte (SHA-256 `d9fba84ca4092d682ee7d190ca05a8a5ef2c286df086a01cebb12e3e2cfbbffd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
