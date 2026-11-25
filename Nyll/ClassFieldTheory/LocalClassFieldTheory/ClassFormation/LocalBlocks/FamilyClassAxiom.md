# The local class-field axiom for finite families of local blocks

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.FamilyClassAxiom`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension whose Galois group is cyclic with generator `σ`, and let `d : ι → LocalPlaceDatum K L` be a finite family of places, each a nontrivial absolute value `v_i` on `K` with a chosen extension `w_i` to `L`. Write `K_i` for the completion of `K` at `v_i` and `L_i` for the algebraic localization `LocalizedCompletion` at `w_i`, which local instances make a finite Galois extension of `K_i`. The file combines the local class-field computations with the description of the product of local blocks `LocalBlockFamily d` as a product of induced modules, giving the finite-family part of the localized class formation.

## Main results

- `localBlockFamilyHerbrandH0EquivNormQuotients`: an isomorphism from `HerbrandH0 Gal(L/K) (LocalBlockFamily d)` to the product over `i` of the norm quotients `NormQuotient K_i L_i`.
- `localBlockFamilyHerbrandH0Finite`, `localBlockFamilyHerbrandHMinusOneFinite`: the degree-zero and degree −1 Herbrand groups of the family are finite.
- `localBlockFamilyHerbrandHMinusOne_card_eq_one`: the degree −1 Herbrand group of the family, taken with respect to `σ`, has cardinality 1.
- `localBlockFamily_herbrandQuotient_eq_product_localDegrees`: the Herbrand quotient of the family, a rational number, equals the product of the local degrees `[L_i : K_i]` (as `Module.finrank`).

The last four results assume, as instance arguments, a `ValuativeRel` on each `K_i` making it a nonarchimedean local field (`IsNonarchimedeanLocalField`). The isomorphism with norm quotients does not.

## Proofs

Each statement is transported along the family isomorphisms `localBlockFamilyHerbrandH0Equiv` and `localBlockFamilyHerbrandHMinusOneEquiv`, or the one-block isomorphisms, to statements about the local units under the decomposition groups. There it rests on the local results `localHerbrandH0EquivNormQuotient`, `localHerbrandH0Finite`, `localHerbrandHMinusOneFinite`, `localHerbrandHMinusOne_card_eq_one` and `localHerbrandH0_card_eq_localDegree`. The Herbrand quotient of the product is the product of the block quotients by `herbrandQuotient_pi`, and each block quotient is `|H⁰| / |H⁻¹|` by `herbrandQuotient_eq_card_ratio`.

## Points to note

- For the finiteness, cardinality and Herbrand-quotient results, all places of the family must have nonarchimedean local completions; archimedean places are outside their scope. The `ValuativeRel` instances are arbitrary arguments, not constructed from the absolute values.
- The field `L_i` is the algebraic localization `LocalizedCompletion`, and the local degree is its dimension over `K_i`.
- The whole group `Gal(L/K)` is assumed cyclic with a given generator; the degree −1 groups depend on that generator.
- `HerbrandH0`, `HerbrandHMinusOne` and `herbrandQuotient` are the library's own notions for multiplicative actions.
- `K` and `L` are taken in `Type` (universe 0); the index type `ι` may lie in any universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/LocalBlocks/FamilyClassAxiom.lean`: the Lean file is the source byte for byte (SHA-256 `7d3f05446c549a691ba9e69d3dd0dfeb9c3e01992a22b32f528b6f3896bc7bc7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
