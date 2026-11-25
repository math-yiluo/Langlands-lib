# Herbrand quotient of the unrestricted factors of a relative S-idele

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Factors`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a cyclic Galois extension of number fields with group `G` and `S` a finite set of finite places of `K`. The unrestricted factors of a relative `S`-idele are the unit groups `(K_v ⊗[K] L)ˣ` at all infinite places `v` and at the finite places `v ∈ S` (`RelativeUnrestrictedSPlaceFactors S`, with `G` acting on the factor `L`). The file transports the Herbrand calculation for the corresponding family of induced local blocks to these factors, through the imported `G`-equivariant isomorphism `relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily`.

## Main results

- `relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily` and `relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily`: the degree 0 and degree −1 groups of the unrestricted factors are isomorphic to those of the local-block family.
- `relativeUnrestrictedSPlaceFactorsHerbrandH0Finite`, `relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite`: both groups are finite when `σ` generates `G`.
- `relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product`: the degree-zero group has order equal to the product over the unrestricted places of the local degrees `relativeUnrestrictedSPlaceLocalDegree S i`.
- `relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one`: the degree −1 group is trivial.
- `relativeUnrestrictedSPlaceFactors_herbrandQuotient`: the Herbrand quotient of the unrestricted factors is the product of the local degrees.

## Proofs

Each statement is the corresponding imported statement for the local-block family, carried across the isomorphisms of cohomology induced by an equivariant group isomorphism (`herbrandH0EquivariantMulEquiv`, `herbrandHMinusOneEquivariantMulEquiv`); the quotient formula then follows from `herbrandQuotient_eq_card_ratio`.

## Points to watch

- The finiteness, cardinality and Herbrand-quotient results assume that `G` is cyclic, through the hypothesis `hgen` that every element is a power of `σ`; the two isomorphisms of cohomology groups do not.
- `K` and `L` are taken in `Type`.
- The local degree at a place is the order of the decomposition group of a chosen place of `L` above it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/Herbrand/Factors.lean`: the Lean file is the source byte for byte (SHA-256 `56fd194396dbc282e558737a03ee0b7ce28a54bfe8c8b4228b7f231f8afc5a35`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
