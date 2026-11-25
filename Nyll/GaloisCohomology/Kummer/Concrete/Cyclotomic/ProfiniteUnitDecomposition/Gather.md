# Gathering the p-adic coordinates into ℤ̂

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

One step in building the decomposition of `ℤ̂ˣ`.

- `gatherFree`: the topological group isomorphism `∏_p ℤ_p ≃ₜ* ℤ̂`, both sides written multiplicatively and `p` running over all primes. It is the inverse of the library's additive isomorphism `ℤ̂ ≃ ∏_p ℤ_p` (`zHatContinuousAddEquivPrimeProduct`), transported to multiplicative notation.

The definition lives in the internal namespace `KummerTheory.ProfiniteUnitDecomposition.Internal`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Gather.lean`: the Lean file is the source byte for byte (SHA-256 `c821170c9bfe27c56cc4aaaf1dd3ae3aeb23fc07ceea3fa48c3139b5dcff0a04`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
