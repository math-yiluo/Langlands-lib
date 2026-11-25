# Quotient of ℤ̂ × T by the closure of its torsion

Module `Nyll.GaloisCohomology.ProfiniteIntegers.CyclotomicTorsionQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file contains the topological-group computation behind the cyclotomic torsion decomposition `Gal(ℚ_cyc/ℚ) ≃ ℤ̂ × f` named in its comments: when the torsion of a commutative topological group `T` is dense in `T`, dividing `ℤ̂ × T` by the closure of its torsion leaves `ℤ̂`. Here `ℤ̂` is the library's `ZHat`, written multiplicatively.

- Instances: multiplication by a nonzero natural number is injective on `ℤ̂` (`HasUniqueDiv ZHat`), so `Multiplicative ZHat` is torsion-free.
- `topologicalClosure_torsion_zHatMul_prod`: if the torsion subgroup of `T` is dense, the closure of the torsion subgroup of `ℤ̂ × T` is `1 × T`.
- `torsionQuotientZHatMulProdEquiv`: under the same hypothesis, the quotient of `ℤ̂ × T` by that closure is isomorphic to `ℤ̂`.

The first projection induces the isomorphism, since its kernel is `1 × T`. The isomorphism is algebraic: no statement about the quotient topology is made. The decomposition of the cyclotomic Galois group itself is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/ProfiniteIntegers/CyclotomicTorsionQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `9a9e8b9f3d27c66c08787ce9053cb757ad631ca00a93c4d0c9fe46e1b76d17c2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
