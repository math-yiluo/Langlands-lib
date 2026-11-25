# The universal norm-descent lemma

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.Universal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file works in the abstract setting of a topological group `G` with a degree datum `D` and a valuation datum `v` on a coefficient representation `A`, written additively. Let `K` be a `FiniteAbstractField G` (finite over the base field) and `L/K` a finite Galois extension. Let `E` and `I` be the maximal unramified extensions of `L` and `K` (`D.maximalUnramifiedField`). Let `φ` be an element of `D.FrobeniusElements`, in the Galois group of `E` over `K`, of Frobenius exponent 1, and let the `τᵢ` lie in the kernel of the normalized degree map on that group. Take units `u` and `uᵢ` of `E` coming from finite levels over `K` that satisfy the relation (hypothesis `hstar`, a sum over a finite set)

`φ·u − u = Σᵢ (τᵢ·uᵢ − uᵢ)`.

The file shows that the norm of `u` to `I` comes from a unit of `K` that is a unit norm from every finite intermediate field.

## Results

- `universalNormDescent_endpoint_descent`: under `hstar` there is a unit `aK` of `K` whose image in `I` is the norm of `u`. This only needs `G` to be a topological group.
- `universalNormDescent_mem_finiteUnitNormRange`: assume further that `G` is compact, Hausdorff and totally disconnected and that `v` satisfies the unit-cohomology axiom. Then every such `aK` lies in `finiteIntermediateUnitNormRange` for every finite intermediate field `M` between `E` and `K`.
- `universalNormDescent`: under the same assumptions, some `aK` maps to the norm of `u` and lies in `infiniteUnitNormSubgroup E K`.

## Proof

The norm of `u` is Frobenius-fixed (`maximalUnramifiedNorm_fixed_of_hstar`), so it descends to `K` (`descend_maximalUnramifiedNorm_unit`).

For the second statement, the fields `M` and `L`, and the finite fields carrying `u` and the `uᵢ`, are placed in a common finite Galois extension `P` of `K`. Let `n = [P : K]` and let `S ⊆ T` be the fixed fields in `E` of `φⁿ` and `φ^(n·n)`. On this tower `universalNormDescent_fixedTower_solution`, which uses the axiom, solves the relation. The norm to `I` of a corrected element then descends to a unit `zK` of `K`. Together with `frobeniusNormIdentities` this gives `aK = N(y) + n·zK` for the norm `N` from `S` to `K`, which shows that `aK` is the norm of a unit of `P`.

## Watch for

- The hypothesis `hAxiom : v.SatisfiesUnramifiedUnitCohomology` assumes the vanishing of `Ĥ⁰` and `Ĥ⁻¹` of units in unramified cyclic extensions. It is not proved.
- `φ` must have Frobenius exponent 1. Normality of `L` over `K` and finiteness of the quotient are instance arguments.
- `infiniteUnitAddSubgroup` contains only the units of `E` that come from some finite intermediate field over `K`. `infiniteUnitNormSubgroup` is the library's group of units of `K` that are unit norms from every finite intermediate field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/Universal.lean`: the Lean file is the source byte for byte (SHA-256 `23481e6b0166d3001d6aa5c90e001eb00f9d542ce681d03833726bae8c644129`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
