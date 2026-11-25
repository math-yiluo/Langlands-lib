# Local Herbrand groups at the unrestricted places of a relative S-idele

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Local`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a Galois extension of number fields with group `G`, and `S` a finite set of finite places of `K`. At each unrestricted place (every infinite place of `K` and every place in `S`) a place of `L` above it has been chosen; its decomposition group acts on the units of the library's local field `LocalizedCompletion`. The file computes the low-degree Tate groups of these local modules, combining finite local class field theory with the explicit real and complex norm calculation.

## Main definitions and results

- `relativeUnrestrictedSPlaceLocalDegree S i`: the order of the decomposition group at the chosen place above `i`. According to the file, at a finite place this is the degree of the localized completion, and at an infinite place it is `1` or `2` according as the place is unramified or ramified.
- `absoluteValueDecompositionGroup_card_eq_localizedDegree`: for a nontrivial absolute value `vK` on `K` and an extension `w` to `L` (here `K`, `L` only need to be fields with `L/K` finite Galois), the decomposition group of `w` has order `[LocalizedCompletion vK w : K_v]`, because it is isomorphic to the Galois group of that local extension.
- `relativeUnrestrictedLocalHerbrandH0Finite`, `relativeUnrestrictedLocalHerbrandHMinusOneFinite`: each local degree 0 and degree −1 group is finite; in degree −1 the generator of the decomposition group is the one derived from `σ` (`subgroupGeneratorOfGenerator`).
- `relativeUnrestrictedLocalHerbrandH0_card_eq_localDegree`: the local degree-zero group has order equal to the local degree.
- `relativeUnrestrictedLocalHerbrandHMinusOne_card_eq_one`: the local degree −1 group is trivial.

## Proofs

Each of the four statements about the local groups splits into the infinite and the finite case. At infinite places it uses the imported archimedean computations (`infinitePlaceLocalHerbrandH0_card_eq_localDegree`, `infinitePlaceLocalClassAxiom_cards`) and the fact that the stabilizer of an infinite place has order `1` or `2`. At finite places it uses the imported local results `localHerbrandH0_card_eq_localDegree` and `localHerbrandHMinusOne_card_eq_one` for the `v`-adic absolute value, together with `absoluteValueDecompositionGroup_card_eq_localizedDegree`.

## Points to watch

- All results except the decomposition-group lemma assume that `G` is cyclic, through the hypothesis `hgen` that every element is a power of `σ`; this also makes every decomposition group cyclic.
- `K` and `L` are taken in `Type`.
- The places of `L` above the places of `K` are chosen, not canonical.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/SPlaces/Herbrand/Local.lean`: the Lean file is the source byte for byte (SHA-256 `c0d4129294eaec31951c407d697c8244a7a5a223eaa7806589185575501b1e07`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
