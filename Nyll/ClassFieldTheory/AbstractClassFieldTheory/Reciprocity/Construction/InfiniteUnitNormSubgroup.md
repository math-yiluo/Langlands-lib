# Universal norm groups of units

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory with valuation data `v` on a `G`-module `A`, the unit group of a finite abstract field is the subgroup of its invariants of valuation zero. For a finite abstract field `K` and a closed subgroup `E` (thought of as an infinite extension of `K`, though no such condition is imposed), this file defines the norms of units from the finite intermediate fields of `E | K` and their intersection, the universal unit norm group, and compares them with the corresponding norm groups without the unit condition.

## Main definitions and results

- `ValuationData.finiteIntermediateUnitNormRange v E K M`: the image `N(M|K) U_M ⊆ A_K` for a finite intermediate field `M` of `E | K`.
- `mem_finiteIntermediateUnitNormRange_of_overfield`: if `P ⊇ M` are finite intermediate fields, the norm from `P` of a unit of `P` lies in `N(M|K) U_M`, by transitivity of norms in the tower `P | M | K` and the fact that norms of units are units.
- `ValuationData.infiniteUnitNormSubgroup v E K`: the intersection of the `N(M|K) U_M` over all finite intermediate fields `M`, written `N(E|K) U_E`; `mem_infiniteUnitNormSubgroup_iff` unfolds it.
- `finiteIntermediateUnitNormRange_le_normRange` and `infiniteUnitNormSubgroup_le_normSubgroup`: the unit norm groups lie in the norm groups `N(M|K) A_M` and their intersection.

## Watch for

`N(E|K) U_E` is defined as an intersection of finite-level norm groups, not as the image of a norm map from `E`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `55ac4921027d49fb5401854548cfd7b7d69eacbb2bc465678ebf41d67fcd8bff`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
