# Multiplicativity of the abstract reciprocity map

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.ReciprocityMapMul`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The endpoint of the multiplicativity argument in the abstract class field theory of the library. For a finite normal extension `L/K` and Frobenius elements `σ₁, σ₂` of `L̃/K` (`L̃` the maximal unramified extension of `L`), the reciprocity map, with values in norm classes of `A_K` written additively, satisfies `r(σ₁σ₂) = r(σ₁) + r(σ₂)`.

## Main result

`reciprocityMap_mul`: let `G` be profinite (compact, Hausdorff, totally disconnected), `A` a `G`-module with valuation data `v` satisfying `hAxiom : v.SatisfiesUnramifiedUnitCohomology D`, `K` of finite absolute degree and `L/K` finite and normal. Then `reciprocityMap (σ₁ * σ₂) = reciprocityMap σ₁ + reciprocityMap σ₂` for all Frobenius elements `σ₁, σ₂`.

## Proof

The file only assembles earlier results.

1. Fix a Frobenius element `φ` of exponent 1 (`chosenDegreeOneFrobeniusElement`), put `σ₃ = σ₁σ₂` and `σ₄ = φ^(n₁) σ₂ φ^(-n₁)`, take chosen prime elements `π₁, π₂, π₃` of the fixed fields of `σ₁, σ₂, σ₃`, and a prime `π₄` of the fixed field of `σ₄` with the same norm to `K` as `π₂` (`exists_primeElement_frobeniusActionConjugate_norm_eq`).
2. The alternating combination `u = s₄ + s₁ − s₃` of Frobenius power sums, and three correction terms (`p₄ − p₃`, `p₁ − p₃`, `p₃ − τ₁·p₃`), are finite-stage units.
3. The power-sum relation `frobeniusPowerSum_mul_action_sub`, rewritten by `frobeniusMultiplicativity_actionDifference_eq_correctionSum`, expresses `φ·u − u` as a sum of terms `τᵢ·cᵢ − cᵢ` with each `τᵢ` of normalized degree zero.
4. `universalNormDescent`, which uses `hAxiom`, then shows that the norm of `u` to the maximal unramified extension of `K` comes from an element of `A_K` in the subgroup of unit norms from the finite stages, hence in the maximal-unramified norm subgroup.
5. `relativeNorm_frobeniusPowerSum_alternating` and `maximalUnramifiedNormClass_add_eq_of_relativeNorm` give `[N π₄] + [N π₁] = [N π₃]`; replacing `N π₄` by `N π₂` and applying `reciprocityMap_mul_of_primeNormClass_eq` concludes.

## Watch for

- The theorem holds under the hypothesis `hAxiom` on the cohomology of unramified units, an axiom of the abstract setting that the theorem carries rather than proves.
- Multiplicativity is stated on Frobenius elements of `L̃/K`, before the map is passed to the Galois group of `L/K`.
- The proof works with the left action of `Rep`, so the conjugate `σ₄` and the order of the remainders differ from the exponent notation of the classical argument.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/ReciprocityMapMul.lean`: the Lean file is the source byte for byte (SHA-256 `9eaa148361a91e6c6c44af45b4e853267f60049193529d087f8c4d3652350515`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
