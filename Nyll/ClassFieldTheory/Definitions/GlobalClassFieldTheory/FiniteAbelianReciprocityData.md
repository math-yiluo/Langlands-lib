# Reciprocity data for a finite abelian extension

Module `Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The ideal-theoretic form of Artin reciprocity for an abelian extension `L/K` of number fields, packaged as a structure of data: a ray-class Artin map normalized by arithmetic Frobenius away from its modulus.

- `FiniteAbelianReciprocityData K L`, for `L/K` abelian Galois, consists of:
  - `modulus`: a ray modulus `m` of `K`;
  - `unramifiedOutsideModulus`: `L/K` is unramified outside `m`;
  - `artin`: a homomorphism `RayClassGroup m →* Gal(L/K)`, surjective (`artin_surjective`);
  - `artin_frobenius`: for every finite prime `v` outside the support of the finite part of `m` and every prime `w` of `L` above `v`, the class of `v` goes to `arithmeticFrobeniusAt w`.

## Points to watch

- The existence of such data is the Artin reciprocity law; this file defines the structure and proves nothing.
- The kernel of the Artin map is not specified, unlike in `RayClassSubgroupRealization`.
- `L` is an abstract number field over `K`, not a subfield of `SeparableClosure K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FiniteAbelianReciprocityData.lean`: the Lean file is the source byte for byte (SHA-256 `f60d01f716049310ec167a212569ba5b2f58539495a4ac7d8512024e220e9e9d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
