# The field norm on unit groups

Module `Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormHom`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The norm of a finite field extension as a homomorphism of multiplicative groups.

- `fieldNormHom K L`: for a finite-dimensional field extension `L/K`, the homomorphism `Lˣ →* Kˣ` induced by Mathlib's `Algebra.norm K`.

## Points to watch

Although the file sits with local class field theory, no hypothesis on `K` or `L` beyond being fields with `L/K` finite is made.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/LocalClassFieldTheory/FieldNormHom.lean`: the Lean file is the source byte for byte (SHA-256 `6c70aa5bf578fd318d2871d0eb7e89d659d88b5a3d32214c9446c0cc7c091350`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
