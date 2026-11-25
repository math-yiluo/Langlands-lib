# Open finite-index subgroups and base data for local existence

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.LocalAbsoluteData`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file collects shared definitions for the finite local existence theorem: a structure for open subgroups of finite index in `Kˣ`, a Galois criterion for fixed fields of closed subgroups of the absolute Galois group, and a finiteness instance for the ground field.

- `OpenFiniteIndexSubgroup K`: a structure bundling a subgroup of `Kˣ` that is open in the topology of `Kˣ` and has finite index, with extensionality (`OpenFiniteIndexSubgroup.ext`) and the partial order lifted from subgroups.
- `abstractFixedField_isGalois_of_base_normal`: for a closed subgroup `H` of `Gal(SeparableClosure K / K)` that is normal inside the abstract `baseField`, the fixed field of `H` is Galois over `K`. Since the base is the whole group, `H` is normal, and infinite Galois theory applies.
- `intrinsicAbstractBase_index_finite`: the ground-field fixing group has finite index in the abstract `baseField` (they coincide).

`OpenFiniteIndexSubgroup` is the library's own structure, and it requires `K : Type` in universe `0`. Nothing about `K` being local is assumed in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean`: the Lean file is the source byte for byte (SHA-256 `574f008e0a96c05b99c54ad0f1178f85f8602cb5eae84a46cf65dd8596343c39`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
