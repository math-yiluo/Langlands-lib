# Norm-class relations for multiplicativity of the reciprocity map

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.NormClassRelation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the abstract class field theory of the library, the reciprocity map sends a Frobenius element `σ` of `L̃/K`, for a finite normal extension `L/K` with maximal unramified extension `L̃`, to the class of `N(Σ/K)(π_Σ)`, where `Σ` is the fixed field of `σ` and `π_Σ` a prime element of it. This file carries out the last steps of the proof that this map turns products of Frobenius elements into sums of classes (the module `A` is written additively): it passes an alternating relation between Frobenius power sums down to `A_K`, then to norm classes, then to the reciprocity map.

## Main results

- `relativeNorm_frobeniusPowerSum_alternating`: for a profinite `G` (compact, Hausdorff, totally disconnected), a finite normal `L/K`, a Frobenius element `φ` of exponent 1 and Frobenius elements `σ₁, σ₂`, put `σ₃ = σ₁σ₂` and `σ₄ = φ^(n₁) σ₂ φ^(-n₁)`. For elements `πᵢ` fixed by the fixed fields `Sᵢ` of `σᵢ` and `u = s₄ + s₁ − s₃` (the Frobenius power sums of the `πᵢ`), the norm of `u` from the maximal unramified extension of `L` to that of `K` equals `N(S₄/K)π₄ + N(S₁/K)π₁ − N(S₃/K)π₃`.
- `maximalUnramifiedNormClass_add_eq_of_relativeNorm`: for `L/K` and `L̃/K̃` finite, `K̃` being the maximal unramified extension of `K`, if `r₁ + r₂ − r₃ ∈ A_K` is the norm of any `u` fixed by `L̃` (hypothesis `hnorm`), and that norm comes from an element of `A_K` lying in the maximal-unramified norm subgroup, then the classes satisfy `[r₁] + [r₂] = [r₃]`.
- `reciprocityMap_mul_of_primeNormClass_eq`: if `π₁, π₂, π₃` are prime elements of the fixed fields of `σ₁, σ₂, σ₁σ₂` and their norm classes satisfy `[N π₁] + [N π₂] = [N π₃]`, then `reciprocityMap (σ₁σ₂) = reciprocityMap σ₁ + reciprocityMap σ₂`.

## Proofs

The first result applies `frobeniusNormIdentities` (norm of a Frobenius power sum equals the norm of the fixed element) to each of the three terms. The second is the criterion that a class vanishes exactly on the norm subgroup. The third rewrites each reciprocity value through `reciprocityValueOfPrime_eq_reciprocityMap`, that is, independence of the prime element chosen.

## Watch for

- `reciprocityMap_mul_of_primeNormClass_eq` takes the needed norm-class equality as the hypothesis `hclasses`; it only converts that equality into the statement about the reciprocity map. Likewise the second result takes the descent of the norm to a universal norm as the hypothesis `huniversal`.
- The third result assumes `hAxiom : v.SatisfiesUnramifiedUnitCohomology D`, the library's axiom on the cohomology of unramified units for the valuation data `v`, and works with fields of finite absolute degree (`FiniteAbstractField`); the first two take `K : FiniteResidueAbstractField D`.
- Norm classes are taken modulo the library's maximal-unramified norm subgroup (`maximalUnramifiedNormClass`), not a Mathlib notion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/NormClassRelation.lean`: the Lean file is the source byte for byte (SHA-256 `fae54ea90778418d8cf48ca63687896ef82392b0805be7371e86ccc92fa22300`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
