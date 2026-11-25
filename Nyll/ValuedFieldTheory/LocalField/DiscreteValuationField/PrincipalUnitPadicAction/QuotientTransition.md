# Additive transition maps between principal-unit quotients

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.QuotientTransition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field with a chosen complete discrete valuation (the library's `CompleteDVF`), the file writes the reduction maps U¹/U^(n+1) → U¹/U^(m+1), for m ≤ n, additively. No finiteness of the residue field and no scalar action is used.

- `Internal.principalUnitQuotientCarrierTransitionAdd F hmn`: the reduction map on the quotients, as an additive homomorphism between their `Additive` forms.
- `DiscretePrincipalUnitQuotient.transition F hmn`: the same map on the wrapper type `DiscretePrincipalUnitQuotient` (the quotient with its discrete topology), and `DiscretePrincipalUnitQuotient.val_transition`, which says its underlying value is the map above.

All levels are shifted by one: level n stands for the quotient by U^(n+1).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitPadicAction/QuotientTransition.lean`: the Lean file is the source byte for byte (SHA-256 `09bfff55f4d05ce25a3d171c01b1ec449308cbc9d90cc51d56ce8020e7a5653a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
