# Open finite-index subgroups of a local field and of its small copy

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkOpenSubgroups`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A nonarchimedean local field `K` in any universe has a small representative `Shrink.{0} K` in universe `0`; smallness comes from `nonarchimedeanLocalField_small` and is installed by a `let` inside each statement. This file transports open finite-index subgroups of the unit group between the two.

- `shrinkUnitsContinuousMulEquiv K`: the unit groups `(Shrink K)ˣ` and `Kˣ` are isomorphic as topological groups, through the ring equivalence of `Shrink` with `K` and the corresponding homeomorphism.
- `shrinkOpenFiniteIndexOrderIso K`: an order isomorphism between `ClassFieldTheory.OpenFiniteIndexSubgroup (Shrink K)` and `ClassFieldTheory.OpenFiniteIndexSubgroup K`, sending a subgroup to its image. Images stay open because a homeomorphism is an open map, and keep finite index because the map is surjective.

`ClassFieldTheory.OpenFiniteIndexSubgroup` is the library's own type, imported here; the proofs use it as a subtype of subgroups carrying openness and finite index.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/ShrinkOpenSubgroups.lean`: the Lean file is the source byte for byte (SHA-256 `a8b8cf000741873fc7b3ca3b1e7b83e0cd2109c933c2fc771c23f32d1669bdf5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
