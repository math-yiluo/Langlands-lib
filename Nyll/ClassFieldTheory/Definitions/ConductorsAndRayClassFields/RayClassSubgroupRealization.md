# Class field of a ray class subgroup

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The class field attached to a subgroup `H` of a ray class group of a number field `K`, packaged as a structure of data; the file constructs none.

- `RayClassSubgroupRealization K m H` consists of:
  - `extension`: a finite abelian extension of `K` inside `SeparableClosure K`;
  - `unramifiedOutsideModulus`: it is unramified outside `m` (`IsUnramifiedOutsideModulus`);
  - `artin`: a homomorphism `RayClassGroup m →* Gal(extension/K)`, surjective (`artin_surjective`) with kernel exactly `H` (`artin_ker`);
  - `artin_frobenius`: for every finite prime `v` outside the support of the finite part of `m` and every prime `w` of the extension lying over `v`, the class of `v` goes to `arithmeticFrobeniusAt w`.

## Points to watch

- This is the library's own notion; the existence of a realization for a given `H` is the existence theorem of class field theory and is not established here.
- For `H` trivial it carries the information of `RayClassFieldRealization` as a surjection with trivial kernel instead of an isomorphism; the file does not relate the two.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassSubgroupRealization.lean`: the Lean file is the source byte for byte (SHA-256 `bc1223d838c295944cb1b4805ee08ff10976ccae50a87d629df0c84f360ab633`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
