# The conductor is the least ray class field modulus

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FullConductorRayClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields and m a modulus of K, with finite part and a set of real places. This file characterizes the full conductor of L/K as the least m whose ray class field contains L.

- `nonempty_algHom_to_rayClassField_iff_fullConductor_le`: there is a K-algebra embedding of L into the ray class field `rayClassField K m` if and only if the full conductor of the norm subgroup N of L/K is at most m. Here the full conductor is `(ideleClassNormConductorialSubgroup).fullConductor`, and the order on moduli compares finite parts and sets of real places.

The proof combines two imported results. The first is the embedding criterion `nonempty_algHom_to_rayClassField_iff_isDefiningModulus`, which says that L embeds into the ray class field of m exactly when C_K^m ⊆ N. The second is the minimality of the full conductor among defining moduli (`isDefiningModulus_iff_fullConductor_le`).

## Points to watch

- `rayClassField K m` is the library's selected ray class field, and containment means existence of a K-algebra map, not inclusion inside a fixed algebraic closure.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/FullConductorRayClassField.lean`: the Lean file is the source byte for byte (SHA-256 `8ba4f7f3bcd9ed81878ed6e54eb00c1e6f36e36836002624258bdeb0462d0114`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
