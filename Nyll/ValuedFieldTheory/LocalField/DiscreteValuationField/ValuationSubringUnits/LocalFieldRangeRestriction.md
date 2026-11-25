# Range restriction for local-field packages

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library's `LocalField K` bundles a complete discretely valued field (`CompleteDVF K`) with finite residue field. The file restricts its valuation to the actual multiplicative range and records the resulting topological properties.

- `LocalField.mrangeRestrict F`: the local-field package whose underlying complete DVF is `CompleteDVF.mrangeRestrictCompleteDVF F.toCompleteDVF`, the same field with the valuation valued in its own range; finiteness of the residue field is carried over.
- `mrangeRestrict_properSpace`: for the normed-field structure on `K` attached to the restricted valuation, `K` is a proper metric space.
- `mrangeRestrict_completeSpace`: for the same structure, `K` is complete.

Both results are direct specializations of the corresponding statements for complete DVFs with finite residue field in the file on the topology of range-restricted complete DVFs.

The normed-field and `Valued` structures in these statements are supplied locally (`letI`) by the definitions `mrangeRestrictValued` and `mrangeRestrict_nontriviallyNormedField`; they are not global instances, so the statements concern that particular topology.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/LocalFieldRangeRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `5c1250e89f92bfbbad3862d35f93604a5f48eb877e65af1d0d14ebceb199c12a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
