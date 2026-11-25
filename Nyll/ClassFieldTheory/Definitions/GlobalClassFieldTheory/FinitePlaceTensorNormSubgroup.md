# Local norm subgroup at a finite place

Module `Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FinitePlaceTensorNormSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The subgroup of local norms at a finite place `v` of a number field `K` for a finite extension `L`, defined through the local algebra `K_v ⊗[K] L`.

- `finitePlaceTensorNormSubgroup K L v`: for a number field `K`, a field `L` finite-dimensional over `K` and a finite prime `v`, the image in `K_vˣ` of the units of `K_v ⊗[K] L` under the determinant norm `Algebra.norm K_v`.

## Points to watch

As the module comment says, the definition keeps the whole algebra `K_v ⊗[K] L`, with all its factors above `v`, and does not choose a single completion `L_w`; the file does not compare it with the norm group of one completion. No `NumberField L` instance is assumed, only finite-dimensionality over `K`, and `L` need not be Galois over `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FinitePlaceTensorNormSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `e0a6f2240757dc87fdbd82c35da10f7c969811c3cda351ee5abad995885b042e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
