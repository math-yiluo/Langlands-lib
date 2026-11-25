# The quotient of ℤ̂ˣ by the closure of its torsion

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `zHatUnitsTorsionQuotientEquiv`: a topological group isomorphism `ℤ̂ˣ ⧸ closure(torsion of ℤ̂ˣ) ≃ₜ* ℤ̂`, the target written multiplicatively.

It is the general construction `torsionQuotientEquivOfZHatMulDecomposition` applied to the decomposition `ℤ̂ˣ ≃ ℤ̂ × ∏_p (finite factor of ℤ_pˣ)` (`zHatUnitsDecomposition`) and to the density of torsion in the second factor `CyclotomicFinitePart`, the product of the finite factors (`dense_torsion_cyclotomicFinitePart`).

The isomorphism depends on the chosen decomposition: the class of `u` goes to the `ℤ̂`-coordinate of `u` in it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/CyclotomicQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `5201584a1e6aa332323447581490fb5e6f6ecb97cdb9b3907e48eb7a70339c16`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
