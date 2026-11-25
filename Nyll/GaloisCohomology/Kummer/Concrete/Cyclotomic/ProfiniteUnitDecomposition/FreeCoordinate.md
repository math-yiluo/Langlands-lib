# The free coordinate of a profinite unit at a prime

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FreeCoordinate`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `zHatUnitsDecomposition_freeCoordinate` (simp lemma): for `u ∈ ℤ̂ˣ` and a prime `p`, the image in `ℤ_p` of the free (`ℤ̂`) coordinate of `u` under `zHatUnitsDecomposition` equals the `ℤ_p` coordinate of the `p`-adic component of `u` in the local decomposition `ℤ_pˣ ≃ (finite factor) × ℤ_p`.

The proof unfolds the decomposition: the free coordinate is assembled from the local ones through `ℤ̂ ≃ ∏_p ℤ_p`, and the projection to `ℤ_p` recovers the `p`-th entry.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/FreeCoordinate.lean`: the Lean file is the source byte for byte (SHA-256 `b80676ea799669ee49babbc7c97a44d3c0dc73be951c5af434f9751b0fe9caa4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
