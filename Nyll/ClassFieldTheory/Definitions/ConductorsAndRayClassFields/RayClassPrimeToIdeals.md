# Fractional ideals prime to a modulus

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassPrimeToIdeals`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The group `I^m` of nonzero fractional ideals of a number field `K` that are prime to the finite part of a ray modulus `m`.

- `rayClassPrimeToIdeals m`: the subgroup of `NumberFieldFractionalIdealGroup K` of those `I` whose exponent `FractionalIdeal.count K v I` vanishes at every finite prime `v` in the support of the finite part of `m`. Closure under products and inverses comes from the additivity of `count`.

## Points to watch

Only the support of the finite part matters: the exponents of `m` and its real places play no role here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassPrimeToIdeals.lean`: the Lean file is the source byte for byte (SHA-256 `80d1d821b8180b0f8f2aa4626714b7edd1bab4e1c85d026f717dc3e5b5ce1b79`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
