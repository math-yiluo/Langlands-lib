# Quotient by closed torsion from a decomposition G ≃ ℤ̂ × T

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `torsionQuotientEquivOfZHatMulDecomposition`: let `G` and `T` be commutative topological groups, `G` compact, and `E : G ≃ₜ* ℤ̂ × T` a topological group isomorphism (`ℤ̂` written multiplicatively) such that the torsion of `T` is dense in `T`. Then `G ⧸ closure(torsion of G) ≃ₜ* ℤ̂`, induced by the first coordinate of `E`.

The proof computes the kernel of `G → ℤ̂` as the closure of the torsion of `G`: `E` carries torsion to torsion and closures to closures, and the closure of the torsion of `ℤ̂ × T` is `1 × T` (a library result, `topologicalClosure_torsion_zHatMul_prod`, which uses the density hypothesis). The algebraic isomorphism is then made topological by the compact-to-Hausdorff criterion.

Compactness of `G` is assumed; the isomorphism depends on `E`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/TorsionQuotientEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `ae4918bc0bebd5a5998446e82cc6a5f33514c0162ae2e862d69558b235164d18`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
