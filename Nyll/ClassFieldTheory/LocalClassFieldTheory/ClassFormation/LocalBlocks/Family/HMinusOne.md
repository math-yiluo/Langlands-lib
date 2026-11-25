# Degree −1 Herbrand group of a finite family of local blocks

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.HMinusOne`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension whose Galois group is cyclic with generator `σ`, and let `d : ι → LocalPlaceDatum K L` be a finite family of places, each a nontrivial absolute value on `K` with a chosen extension `w` to `L`. The file computes the Herbrand group in degree −1 of the product `LocalBlockFamily d` of local blocks.

- `localBlockFamilyHerbrandHMinusOneEquiv`: for `Fintype ι`, a multiplicative isomorphism from `HerbrandHMinusOne Gal(L/K) (LocalBlockFamily d) σ` to the product over `i` of `HerbrandHMinusOne` of the decomposition group at `w_i` acting on the units of `LocalizedCompletion`, taken with respect to the generator `subgroupGeneratorOfGenerator` of that subgroup derived from `σ`.

It composes `herbrandHMinusOnePiEquiv` (the degree −1 group of a product) with the one-block isomorphisms `localPlaceBlockHerbrandHMinusOneEquiv`.

The degree −1 group depends on the generator: each factor uses the induced generator of the decomposition group, not `σ`. The actions are local instances fixed in the statement; `HerbrandHMinusOne` is the library's own Herbrand group.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalBlocks/Family/HMinusOne.lean`: the Lean file is the source byte for byte (SHA-256 `0d9ff6fd7fb98a8806a2f8369ad045530f141013ee4a8e706baa22285e990763`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
