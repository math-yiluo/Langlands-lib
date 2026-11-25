# Everywhere local norms

Module `Nyll.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition that an element of a number field `K` is a local norm from a finite extension `L` at every place of `K`.

- `IsEverywhereLocalNorm K L x`: for `x ∈ Kˣ`, `IsNormAtFinitePlace K L w x` holds at every finite prime `w` and `IsNormAtInfinitePlace K L w x` at every infinite place `w`; in each case `x` is the determinant norm of a unit of `K_w ⊗[K] L`.

## Points to watch

Local norms are taken from the algebra `K_w ⊗[K] L`, not from a chosen completion of `L`. `L` need only be a field finite-dimensional over `K`. No Hasse norm statement is made here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/NormTheorems/IsEverywhereLocalNorm.lean`: the Lean file is the source byte for byte (SHA-256 `5d80818b233d74c364600f1d62f7c7e734d2e7641df49f8171134b008524b91e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
