# Product equivalences for the decomposition of profinite units

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Basic pieces for the topological decomposition of `ℤ̂ˣ` used in the rational cyclotomic computation.

- `continuousMulEquivPiCongr`: a family of topological multiplicative equivalences `A i ≃ₜ* B i` gives one on the products `∏ A i ≃ₜ* ∏ B i`.
- `continuousMulEquivPiProd`: `∏ (A i × B i) ≃ₜ* (∏ A i) × (∏ B i)`.
- `continuousPiMultiplicative`: `Multiplicative (∏ A i) ≃ₜ* ∏ Multiplicative (A i)`, with product topologies.
- `CyclotomicFinitePart`: the product over all primes `p` of `padicUnitFiniteFactor p`, the finite factor in the library's decomposition of the `p`-adic units `ℤ_pˣ`.
- An instance `Fact p.Prime` for `p : Nat.Primes`, in the internal namespace of the decomposition.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `3708e99a5a2021547df63c75cc089b173dc9fb480e09ef4959b1e3a0b4562edb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
