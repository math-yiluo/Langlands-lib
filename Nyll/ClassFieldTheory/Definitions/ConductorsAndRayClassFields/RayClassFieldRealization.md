# Ray class fields as data

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A ray class field of a number field `K` for a modulus `m` is packaged as a structure of data; the file constructs none.

- `RayClassFieldRealization K m` consists of:
  - `extension`: a finite abelian extension of `K` inside `SeparableClosure K` (`FiniteAbelianExtension K`);
  - `unramifiedOutsideModulus`: it is unramified outside `m`, in the sense of `IsUnramifiedOutsideModulus`;
  - `artinEquiv`: a group isomorphism from the ideal-theoretic ray class group `RayClassGroup m` onto `Gal(extension/K)`;
  - `artin_frobenius`: for every finite prime `v` outside the support of the finite part of `m` and every prime `w` of the extension lying over `v`, `artinEquiv` sends the class of `v` to `arithmeticFrobeniusAt w`.

## Points to watch

- This is the library's own notion. The existence of a realization for a given `m` is the existence theorem of class field theory and is not established here; nor is uniqueness.
- The Frobenius element is Mathlib's chosen arithmetic Frobenius lift; the condition is imposed for every `w` above `v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassFieldRealization.lean`: the Lean file is the source byte for byte (SHA-256 `0bc85309e9bfe20af0a307c0328c1904418cc76b8571821564ba28db6f8098aa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
