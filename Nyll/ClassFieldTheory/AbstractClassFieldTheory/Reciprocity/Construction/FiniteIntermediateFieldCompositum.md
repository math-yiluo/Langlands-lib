# Degree and common composita of finite intermediate fields

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Two facts about finite intermediate fields `M` of an extension `E / K` of abstract fields (closed subgroups `M` of `G` between `E` and `K`, of finite index in `K`), used by the norm-descent tower.

- `FiniteIntermediateField.quotientCard M`: the cardinality of the finite quotient of `K` by the extension subgroup of `M`, that is, the degree of `M` over `K`. The finiteness instance carried by `M` is built into the definition, so later constructions need no separate finiteness hypothesis. `quotientCard_pos` says it is positive.
- `FiniteIntermediateField.exists_common_compositum`: given one finite intermediate field `M` and a finite family `F i` (`i` in a `Finset`), there is a finite intermediate field `P` containing `M` and every `F i`, stated as `P ≤ M` and `P ≤ F i` on the subgroup side. It is proved by induction on the finite set, taking successive composita.

The result is existential: no particular compositum, and no ordering of the family, is chosen.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean`: the Lean file is the source byte for byte (SHA-256 `a5a74d90ff2c480913aafe2808df124fc3ccfa3079f84c61bdba8cc4ede6cadb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
