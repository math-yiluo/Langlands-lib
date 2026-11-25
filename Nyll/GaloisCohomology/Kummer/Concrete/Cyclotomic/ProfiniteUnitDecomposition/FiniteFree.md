# Regrouping finite and free coordinates of profinite units

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

One step in building the decomposition of `ℤ̂ˣ`.

- `finiteFreeSplit`: the topological group isomorphism `∏_p (F_p × ℤ_p) ≃ₜ* (∏_p ℤ_p) × (∏_p F_p)`, where `F_p` is the finite factor `padicUnitFiniteFactor p` of `ℤ_pˣ`, `ℤ_p` is written multiplicatively, and `p` runs over all primes. It only separates the two coordinates and swaps their order.

The definition lives in the internal namespace `KummerTheory.ProfiniteUnitDecomposition.Internal`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/FiniteFree.lean`: the Lean file is the source byte for byte (SHA-256 `204b4ef7200cff5b224d62fb6a6db63789c7a0e07e7cd51b88fb83df64f43cb3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
