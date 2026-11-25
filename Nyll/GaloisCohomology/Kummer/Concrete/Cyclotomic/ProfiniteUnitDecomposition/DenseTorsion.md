# Density of torsion in a product of finite groups

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.DenseTorsion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `dense_torsion_pi_of_finite`: in an arbitrary product of finite commutative groups, each carrying a topology, with the product topology, the torsion elements form a dense subset. No condition is put on the topology of the factors.
- `dense_torsion_cyclotomicFinitePart`: in particular, torsion is dense in `CyclotomicFinitePart`, the product over all primes of the finite factors of the `p`-adic unit groups.

The proof takes a basic open set, which restricts finitely many coordinates, and replaces all other coordinates of a point in it by `1`; the result has finite order, a divisor of the product of finitely many element orders.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/DenseTorsion.lean`: the Lean file is the source byte for byte (SHA-256 `de374d72131fb7ea9520417e6c7748e3c56163ec68eb58e3960efefd06a1591a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
