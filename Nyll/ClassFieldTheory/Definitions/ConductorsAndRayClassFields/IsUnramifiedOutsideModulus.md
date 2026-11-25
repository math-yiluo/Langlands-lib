# Unramified outside a modulus

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition that an extension of number fields `L/K` ramifies only at places named by a ray modulus of `K`.

- `IsUnramifiedOutsideModulus K L m`: for number fields `K`, `L` with `L` a `K`-algebra and a ray modulus `m` of `K`, every finite prime `v` of `K` outside the support of the finite part of `m` is unramified in `𝓞 L` (Mathlib's `Algebra.IsUnramifiedIn`), and every real place of `K` outside the infinite part of `m` is unramified in `L` (Mathlib's `InfinitePlace.IsUnramifiedIn`).

## Points to watch

As the docstring says, only the support of the finite part of `m` is used: the exponents of `m` play no role, so the predicate does not say that the conductor divides `m`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/IsUnramifiedOutsideModulus.lean`: the Lean file is the source byte for byte (SHA-256 `4c02bb12977be7ec8505b111b1ebc6923e99955efb59d18bcdee0ba526ad1581`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
