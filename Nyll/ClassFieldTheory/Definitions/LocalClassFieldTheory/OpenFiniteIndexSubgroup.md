# Open subgroups of finite index in `Kˣ`

Module `Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A name for the open subgroups of finite index of the multiplicative group of a field with a topology; the file belongs to the definitions of local class field theory.

- `OpenFiniteIndexSubgroup K`: for a field `K` with a topology, the subtype of subgroups `H` of `Kˣ` that are open and of finite index (`Subgroup.FiniteIndex`). Its order is inclusion of subgroups.

## Points to watch

Openness refers to the topology Mathlib puts on the units `Kˣ`; the definition only asks for a topological space structure on `K`, not that `K` be a topological field or a local field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/LocalClassFieldTheory/OpenFiniteIndexSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `944181b6968b9f502f2c96645c26b9a812c4e0655ca02213314146d510a81a3d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
