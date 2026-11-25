# The norm topology

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory over a group `G` equipped with a topology, with a module `A : Rep ℤ G`, the fixed elements A_K of a closed subgroup K carry the norm topology: the subgroups of norms from A_L, for L/K finite Galois, form a basis of neighbourhoods of zero. This file defines the topology and proves its basic properties.

## Definitions and results

- `FiniteGaloisSubextension.normSubgroup A L`: the subgroup of A_K of norms from A_L; the norm subgroup of a compositum lies in both (`normSubgroup_compositum_le_left`, `_right`), so the family is directed downward.
- `normFilterBasis`, `normTopology A K`: the additive-group filter basis of all norm subgroups and the topology it defines.
- `WithNormTopology A K`: a copy of A_K carrying the norm topology as its instance, with its additive group structure and `withNormTopologyEquiv` back to A_K.
- `IsNormOpen`, `IsNormClosed`, `IsNormHausdorff`, `IsContinuousFromNormTopology`, `IsNormContinuous`: openness, closedness, Hausdorffness and continuity for the norm topology.
- `normTopology_addSubgroup_isOpen_iff`: a subgroup is open if and only if it contains some norm subgroup; in particular every norm subgroup is open (`normSubgroup_isOpen`).
- `universalNormSubgroup A K`: the intersection of all norm subgroups. `normTopology_hausdorff`: the norm topology is Hausdorff if and only if this intersection is zero.
- `normTopology_open_iff_closed_finiteIndex_of_finite_normQuotients`: if every quotient of A_K by a norm subgroup is finite, a subgroup is open if and only if it is closed and of finite index.

## Points to watch

- The norm topology is not put as an instance on A_K itself; statements go through the wrapper type `WithNormTopology` or the predicates above.
- The last theorem takes the finiteness of all norm quotients as the hypothesis `hfinite`; the file does not prove it (the comment says it comes from the abstract reciprocity theorem).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/NormTopology.lean`: the Lean file is the source byte for byte (SHA-256 `1a6861e69b5ea2599b1ea8c6cbe9190bbed9c54d1ca1948f78d2b38569da798a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
