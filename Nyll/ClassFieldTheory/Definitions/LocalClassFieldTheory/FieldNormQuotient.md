# The norm quotient of a field extension

Module `Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The quotient of the multiplicative group of a field by the norms from a finite extension.

- `FieldNormQuotient K L`: an abbreviation for `Kˣ ⧸ fieldNormSubgroup K L`, the quotient of `Kˣ` by the subgroup of norms from `Lˣ`, for any finite-dimensional field extension `L/K`.

## Points to watch

No topology or local field hypothesis is involved, and nothing about the quotient (finiteness, order) is proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `b393b32ba5a9242f0bd8cd29f63de0579bd1d898367ed84ffb628aafc056967a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
