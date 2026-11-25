# Prime elements of Frobenius fixed fields differ by units

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.PrimeUnitDifferences`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class field theory of the library, with a module `A` written additively and valuation data `v`, the fixed field `Σ` of a Frobenius element `σ` of `L̃/K` has prime elements. This file shows that, once embedded in the invariants `A(L̃)` of the maximal unramified extension `L̃` of `L`, any two such primes, or a prime and a Galois translate of it, differ by a unit of some finite stage. Both results are steps in the proof that the reciprocity map is multiplicative.

## Main results

Both results assume `G` profinite (compact, Hausdorff, totally disconnected), `K` of finite absolute degree, and `L/K` finite and normal.

- `frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup`: if `πσ` and `πτ` are prime elements of the fixed fields of Frobenius elements `σ` and `τ`, then `πσ − πτ`, read in `A(L̃)`, lies in `v.infiniteUnitAddSubgroup`, the subgroup of elements that come from a unit of a finite extension of `K` inside `L̃`.
- `frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup`: if `π` is a prime element of the fixed field of `σ` and `q` is any element of `Gal(L̃/K)`, the quotient of `K` by `D.extensionInertiaWithin K.field L hLK`, then `π − q·π` lies in the same subgroup.

## Proofs

For two primes, the finite stage is the compositum of the finite intermediate fields attached to the two fixed fields. It is unramified over both fixed fields because each fixed field has the inertia of `L` (`frobeniusFixedField_fieldInertia`). Prime elements stay prime in unramified extensions (`prime_of_unramified`), and a difference of two primes of the same field is a unit (`sub_mem_unitAddSubgroup_of_prime`). For a translate, the stage is a finite Galois refinement of the fixed field, normal over `K`, so a representative of `q` acts on it and preserves valuations (`valuationAt_normalExtensionAction`).

## Watch for

- The second result acts through a chosen representative of `q` in `K` (`Quotient.out`); the statement itself only involves `q`.
- Units, primes and valuations are the library's axiomatic notions from `ValuationData`, not Mathlib's.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/PrimeUnitDifferences.lean`: the Lean file is the source byte for byte (SHA-256 `4eb92151934018f6155d25208e0551731993866f63e75fdbe0370a316b70fb99`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
