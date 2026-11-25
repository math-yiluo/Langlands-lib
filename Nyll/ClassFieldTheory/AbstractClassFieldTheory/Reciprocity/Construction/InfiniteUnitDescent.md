# Units of the maximal unramified extension and their descent

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory with valuation data `v` on a `G`-module `A`, units are defined only for abstract fields of finite index. This file defines the unit group of an infinite extension `E` of a finite abstract field `K` as the elements that are units at some finite stage, shows that for `E = L̃` (the maximal unramified extension of `L`) it is stable under the action of `G(L̃ | K)` and under the norm to `K̃`, and proves that a norm fixed by a degree-one Frobenius descends to a unit of `K`.

## Main definitions and results

- `FiniteIntermediateField.toFiniteAbstractFieldExtension` and `toFiniteAbstractField`: a finite intermediate field `M` of `E | K` as a finite extension of `K` and as a finite abstract field.
- `descend_maximalUnramified_fixed_unit_of_finiteSupport`: the unit version of the descent criterion of the preceding file. If `a ∈ A_K̃` comes from a unit of a finite Galois intermediate field `P` of `L̃ | K` and is fixed by a Frobenius element `φ` of exponent one, then `a` comes from a unit of `K`.
- `ValuationData.IsFiniteStageUnit v E K a`: `a ∈ A_E` is the image of a unit of some finite intermediate field `M` of `E | K`.
- `ValuationData.infiniteUnitAddSubgroup v E K hEK`: the subgroup `U_E` of these elements, closed under sums by passing to composita; `mem_infiniteUnitAddSubgroup_iff` unfolds it.
- `frobeniusQuotientAction_mem_infiniteUnitAddSubgroup`: the action of every `q ∈ G(L̃ | K)` preserves `U_L̃`; `frobeniusPowerSum_mem_infiniteUnit_universalNormDescent` deduces this for Frobenius power sums.
- `maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup`: for `L | K` finite, the norm `N(L̃|K̃)(a)`, included back into `A_L̃`, lies in `U_L̃` when `a` does.
- `descend_maximalUnramifiedNorm_unit`: for `L | K` finite, `a ∈ U_L̃` and `N(L̃|K̃)(a)` fixed by a Frobenius element of exponent one, there is a unit of `K` whose image in `A_K̃` is `N(L̃|K̃)(a)`.

## Proofs

Descent of units combines the element-level descent with the tower formula for the normalized valuation: if the image of `b ∈ A_K` in `A_P` has valuation zero, then `[P : K]` times the valuation of `b` is zero, hence so is the valuation of `b`. Stability under the action replaces the finite support by its Galois refinement, which the chosen representative preserves. The norm is written as the sum over `G(L̃ | K̃)` of translates, each a unit.

## Watch for

- `U_E` is the library's own notion: a union of finite-level unit groups, defined through `IsFiniteStageUnit`, not via a valuation on `A_E`.
- The descent statements require `φ` of exponent exactly one.
- The stability and descent results take `G` a topological group and `L ≤ K` closed with `G_L` normal in `G_K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean`: the Lean file is the source byte for byte (SHA-256 `0dff61b01a3a14534641c694cfd51af222534aa4c185e5d1c68d031e72564dcd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
