# Units of ℤ̂

Module `Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerUnits`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file upgrades the Chinese remainder isomorphism `ℤ̂ ≅ ∏_p ℤ_p` (over all primes, with `ℤ̂` the library's `ZHat`) to isomorphisms of topological groups and monoids, and deduces the decomposition of the unit group.

- `zHatContinuousMulEquivPrimeProduct`: `ℤ̂ ≃ₜ* ∏_p ℤ_p`, as a topological multiplicative monoid isomorphism.
- `zHatContinuousAddEquivPrimeProduct`: the same map as a topological additive isomorphism.
- `zHatUnitsContinuousMulEquivPrimeProduct`: `ℤ̂ˣ ≃ₜ* ∏_p ℤ_pˣ`, as topological groups.
- `zHatUnitsContinuousMulEquivPrimeProduct_coe_apply`: on a unit, the `p`-th component is its `p`-adic coordinate `zHatToPadicInt p`.

Continuity of the inverse comes from the map being a continuous bijection from a compact space to a Hausdorff space. The unit statement applies the induced map on units and Mathlib's identification of the units of a product with the product of the units (`ContinuousMulEquiv.piUnits`); the unit groups carry Mathlib's topology on units.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerUnits.lean`: the Lean file is the source byte for byte (SHA-256 `745f8dbff15e41378b437b544bfa1b953324b8adc2b6a1dfd62b375521f4f20f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
