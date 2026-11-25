# Restricting a valuation to its multiplicative range

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation `v` on a field with values in a linearly ordered commutative group with zero `Γ`, the file defines the same valuation with codomain the submonoid of values actually taken, and shows that this changes neither the valuation ring, the maximal ideal nor the residue field.

## Definitions and results

- `WithZeroValuation.mrangeRestrict v`: the valuation `r ↦ v r` into `MonoidHom.mrange v`; `mrangeRestrict_apply` says it agrees with `v` after coercion.
- `mem_mrangeRestrict_valuationSubring_iff`: the two valuations have the same valuation ring as sets.
- `valuationSubringEquivMrangeRestrict v`: the resulting ring isomorphism between the two valuation rings (the identity on elements).
- `valuationSubringEquivMrangeRestrict_mem_maximalIdeal_iff` and `valuationSubringEquivMrangeRestrict_map_maximalIdeal`: this isomorphism matches the maximal ideals, and the image of one maximal ideal is the other.
- `residueFieldEquivMrangeRestrict v`: the induced isomorphism of residue fields.

All statements are about valuations on fields (the definition itself needs only a field `R`). The point of the construction, according to the file, is to normalize the value group before arguments that need it to be the actual range, such as closedness of finite-dimensional subspaces.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/RangeRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `95fae19e29f07a506c91da5ce599baa9ce64a78e30970913b7486a5e887d4825`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
