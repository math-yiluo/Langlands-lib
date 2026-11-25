# Families of local idele blocks

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.Instances`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K`, the file sets up the data for combining local induced-module calculations over a family of places, the finite-support part of the localized class formation.

- `LocalPlaceDatum K L`: a structure holding a nontrivial absolute value `base` on `K` with values in `ℝ` and a chosen extension `extension` of it to `L`.
- `LocalBlockFamily d`: for `d : ι → LocalPlaceDatum K L`, the product over `i` of the local blocks `LocalPlaceBlock` attached to `d i`.
- `localBlockFamilyLocalAction`, `localBlockFamilyBlockAction`, `localBlockFamilyCohomologyAction`: the action of each decomposition group on the local units, the induced action of `Gal(L/K)` on each block, and the componentwise action on the product.
- `localBlockFamilyDecompositionFintype`: a `Fintype` structure on each decomposition group, obtained from its finiteness.

These actions are reducible definitions, not global instances; files that use them install them with `letI`. No finiteness is imposed on the index type `ι` here; the cohomology computations in the companion files assume `Fintype ι`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalBlocks/Family/Instances.lean`: the Lean file is the source byte for byte (SHA-256 `2666abb043545169ff3ac28bd58277646311aac66f1da96e066036d86cf9267e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
