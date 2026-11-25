# Decomposition, inertia and ramification groups are closed

Module `Nyll.ValuedFieldTheory.Ramification.ClosedSubgroups`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an algebraic extension `L / K`, possibly infinite, and a valuation ring `A` of `L`, the file proves that the decomposition group, the inertia group and the ramification group of `A` are closed in `Aut_K(L)` with the Krull topology. For Galois `L / K` it deduces that the inertia and ramification fields correspond to these groups under the infinite Galois correspondence.

## Main results

- `decompositionGroup_isClosed`: the group of `σ` with `σ(A) = A` is closed.
- `inertiaGroupInAut_isClosed`: the inertia group, viewed in `Aut_K(L)`, is closed.
- `ramificationGroupInAut_isClosed`: the ramification group, viewed in `Aut_K(L)`, is closed.
- `inertiaField_fixingSubgroup_eq`, `ramificationField_fixingSubgroup_eq`: for `L / K` Galois, the subgroup fixing the inertia (resp. ramification) field is the inertia (resp. ramification) group.

The groups and fields are defined in an imported file. Each proof shows the complement open: if `σ` fails the defining condition, one element `x` of `L` witnesses it (`σ` moves `A`, acts nontrivially on the residue of `x`, or moves the class of a unit `x`), and the same failure holds on the coset of `σ` by the open subgroup fixing `K(x)`. The Galois statements then follow from Mathlib's infinite Galois correspondence for closed subgroups.

## Watch for

No Galois correspondence statement is given for the decomposition field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean`: the Lean file is the source byte for byte (SHA-256 `5951a328cf1835ba3c98c1abb58b8ddb00f2bc77a83f59bac124659c7332ef4d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
