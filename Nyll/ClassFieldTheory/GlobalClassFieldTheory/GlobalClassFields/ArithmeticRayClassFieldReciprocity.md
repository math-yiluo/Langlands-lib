# Arithmetic reciprocity for ray class fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticRayClassFieldReciprocity`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K` and a modulus `m : RayClass.Modulus K`, the library selects a ray class field `rayClassField K m` whose idele norm group is the congruence subgroup `C_K^m` of the idele class group. This file gives the reciprocity isomorphism `Gal(K^m / K) ≃ₜ* C_K / C_K^m` with the arithmetic Frobenius normalization.

- `arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup m`: an isomorphism of topological groups `Gal(K^m / K) ≃ₜ* RayClass.RayClassGroup m`. The Galois group has the Krull topology, the ray class group its quotient topology. It is arithmetic global reciprocity followed by the identification of the quotient of `C_K` by the norm range from `K^m` with `C_K ⧸ C_K^m`; both quotients are discrete, the second because `C_K^m` is open.
- `..._globalNormResidue` (simp): the arithmetic norm-residue symbol of an idele class `c` goes to the ray class of `c`.
- `..._symm_mk` (simp): the inverse sends the ray class of `c` to the norm-residue symbol of `c`.

The ray class field is a specific selected field, and its norm range is imported. The ray class group is the idelic quotient `C_K ⧸ C_K^m`, not a group of ideals.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ArithmeticRayClassFieldReciprocity.lean`: the Lean file is the source byte for byte (SHA-256 `9a1830dce4bbba22cbde9f00766a92ce332e9ddcd776fdb5373ff4e764ccf859`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
