# Local integer units above a finite place as an induced module

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of number fields with group `G`, `vK` a nontrivial nonarchimedean absolute value on `K`, and `w` an extension of `vK` to `L`, with decomposition group `D_w`. Write `E = LocalizedCompletion vK w` for the library's local field attached to `w`, on whose integer units `D_w` acts.

- `completionProductIntegerUnitsEquivInducedModule vK hvK hvKna w`: a group isomorphism from the product, over all extensions `w'` of `vK` to `L`, of the unit groups of the valuation rings of the completions at `w'`, to the module `InducedModule` induced from `D_w` to `G` by `𝒪[E]ˣ`.

The construction reindexes the extensions of `vK` by the right cosets of `D_w` (`rightCosetExtensionEquiv`), transports each valuation ring to `𝒪[E]` along the coset transport `rightCosetCompletionIntegersRingEquivLocalized`, and reads the result in the coordinates of the induced module on right cosets (`inducedRightCosetCoordinates`).

The isomorphism depends on the chosen coset representatives. Its compatibility with the Galois actions is not addressed in this file. `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/OutsideIntegralInduced/LocalInduction/Equiv.lean`: the Lean file is the source byte for byte (SHA-256 `b7663301670761d9422f3696a6962b3163402ea9fc27c5faafaf7b54d88cf4e9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
