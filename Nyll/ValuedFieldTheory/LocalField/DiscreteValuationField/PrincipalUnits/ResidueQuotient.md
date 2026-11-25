# O^*/U¹ is the unit group of the residue field

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O and residue field k, the file identifies the units modulo the first principal units with k^*.

- `residueUnitHom_ker_eq`: the kernel of the reduction homomorphism O^* → k^* is U¹.
- `unitsModOneEquivResidueFieldUnits F`: the group isomorphism O^*/U¹ ≃ k^*, sending the class of u to its residue (`unitsModOneEquivResidueFieldUnits_mk`). Surjectivity comes from the fact that units of a local ring lift through a surjective local homomorphism.
- `unitsModOneEquivResidueFieldUnits_unitsModPrincipalUnitEquivOfPreserves_one`: for a field automorphism `e` of `K` that preserves O (hypothesis `hmem`: x ∈ O ↔ e x ∈ O), the automorphism `e` induces on O^*/U¹ corresponds, under this isomorphism, to the automorphism it induces on k^*.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/ResidueQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `8c60d694dd077527e6e274dcee3ce428dcc362ea9f4a6ca5d02cdf7382069305`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
