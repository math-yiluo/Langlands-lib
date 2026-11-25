# Low-degree Tate groups under equivariant isomorphisms

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

An isomorphism `e : A ≃* B` of multiplicative `G`-modules, `G` finite, that is equivariant (`he : ∀ g a, e (g • a) = g • e a`) matches fixed points, norm kernels, norm images and augmentation images. The file turns this into isomorphisms of the library's groups `HerbrandH0` and `HerbrandHMinusOne` and into equality of Herbrand quotients. Its comment says this lets calculations on field units or local coordinates be applied to their images in idele groups.

## Main definitions and results

- `equivariantMulEquiv_map_tateNorm`, `equivariantMulEquiv_map_sigmaMinusOne`: `e` commutes with the norm and with `σ − 1`.
- `fixedSubgroupEquivariantMulEquiv`, `normKernelEquivariantMulEquiv`: the restrictions of `e` to fixed subgroups and to norm kernels.
- `herbrandH0EquivariantMulEquiv e he : HerbrandH0 G A ≃* HerbrandH0 G B`, computed on classes by `herbrandH0EquivariantMulEquiv_mk`, and `herbrandHMinusOneEquivariantMulEquiv e he σ` in degree −1.
- `herbrandH0Finite_of_equivariantMulEquiv`, `herbrandHMinusOneFinite_of_equivariantMulEquiv`: finiteness passes from `A` to `B`.
- `herbrandQuotient_eq_of_equivariantMulEquiv`: if both groups of `A` are finite, `A` and `B` have the same Herbrand quotient; the finiteness instances for `B` are built inside the statement from the two previous results.

Each equivalence is produced by `quotientMulEquivOfSplit` from the restricted isomorphism and its inverse.

## Points to watch

- No cyclicity is assumed and `σ` is arbitrary.
- `A` and `B` may lie in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/EquivariantEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `27740c8d76e039eeaa4376e0b3e7b96aea24c8be1737021603756c5bbcaf318f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
