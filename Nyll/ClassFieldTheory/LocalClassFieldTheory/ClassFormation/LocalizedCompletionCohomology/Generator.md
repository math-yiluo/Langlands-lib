# A generator of the local Galois group

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension whose Galois group is cyclic with generator `σ`, `v` a nontrivial absolute value on `K` with completion `K_v`, and `w` an extension of `v`, with algebraic localization `L_w = LocalizedCompletion v w`. The file produces a generator of `Aut(L_w/K_v)` from `σ`.

- `localizedCompletionDecompositionGroupFintype`: the `Fintype` structure on the decomposition group of `w` used in the local cohomology computations.
- `localizedCompletionGaloisGenerator`: the `K_v`-automorphism of `L_w` corresponding, under `decompositionGroupEquivAlgebraicLocalizationAut`, to the generator `subgroupGeneratorOfGenerator` of the decomposition group obtained from `σ`.
- `localizedCompletionGaloisGenerator_generates`: every `K_v`-automorphism of `L_w` is a power of this element.

The proof transports `subgroupGeneratorOfGenerator_generates` along the isomorphism between the decomposition group and `Aut(L_w/K_v)`.

The generator depends on the chosen `σ`, and no local-field hypothesis on `K_v` is needed here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalizedCompletionCohomology/Generator.lean`: the Lean file is the source byte for byte (SHA-256 `691ea1a0f767483fd8e0e07a9b59fee6cea0d9dd32afc0080e95a47ebb833014`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
