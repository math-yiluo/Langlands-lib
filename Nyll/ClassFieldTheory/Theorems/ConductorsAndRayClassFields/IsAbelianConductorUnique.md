# Uniqueness of the conductor

Module `Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K and L be number fields with L a K-algebra. A ray class modulus `c` of K satisfies the library's predicate `IsAbelianConductor K L c` when it characterizes exactly the moduli whose ray class fields contain L: a modulus has this property if and only if it is at least `c`.

`IsAbelianConductor.unique`: if `c` and `d` both satisfy `IsAbelianConductor K L`, then `c = d`.

The proof is antisymmetry of the order on moduli: applying the characterization of `c` to `d`, and that of `d` to `c`, gives `c ≤ d` and `d ≤ c`.

The theorem assumes no abelian or Galois hypothesis on L/K; it only uses the shape of the predicate. Existence of such a modulus is a separate result.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/IsAbelianConductorUnique.lean`: the Lean file is the source byte for byte (SHA-256 `28a821826732a42f5fda2bfab76b7ed59c1420110805d18f932dc9f34e37479a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
