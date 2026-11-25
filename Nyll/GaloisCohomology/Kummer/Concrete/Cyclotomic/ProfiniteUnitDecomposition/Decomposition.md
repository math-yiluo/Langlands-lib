# The decomposition of ℤ̂ˣ into a free and a finite part

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `zHatUnitsDecomposition`: a topological group isomorphism `ℤ̂ˣ ≃ₜ* ℤ̂ × CyclotomicFinitePart`, where `ℤ̂` is written multiplicatively and `CyclotomicFinitePart` is the product over all primes `p` of the finite factor of `ℤ_pˣ`.

It is the composite of `ℤ̂ˣ ≃ ∏_p ℤ_pˣ`, the inverse of the product of the local decompositions `(finite factor) × ℤ_p ≃ ℤ_pˣ`, the regrouping into `(∏_p ℤ_p) × (∏_p finite factors)`, and the identification `∏_p ℤ_p ≃ ℤ̂` on the first factor.

The free coordinate is built from the library's chosen local decompositions of `ℤ_pˣ`, not intrinsically.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Decomposition.lean`: the Lean file is the source byte for byte (SHA-256 `d7457fdd790912898f188b89bbe636dd6d9a71d375367b4b09432f76a0072e80`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
