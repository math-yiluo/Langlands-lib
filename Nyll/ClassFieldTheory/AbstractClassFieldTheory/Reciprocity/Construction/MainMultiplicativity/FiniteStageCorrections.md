# Finite-stage units in the multiplicativity correction

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FiniteStageCorrections`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A step in the proof that the abstract reciprocity map is multiplicative, for a profinite group `G` (compact, Hausdorff, totally disconnected), a `G`-module `A`, a degree map `D` and valuation data `v`. Let `K` be a finite abstract field, `L | K` finite Galois, `φ`, `σ₁`, `σ₂` Frobenius elements of `G(L̃ | K)`, `σ₃ = σ₁σ₂`, and `σ₄` the conjugate Frobenius element `frobeniusActionConjugate φ σ₂ d(σ₁)` of an earlier file. Take prime elements `π₁`, `π₃`, `π₄` of the fixed fields of `σ₁`, `σ₃`, `σ₄`, with images `p₁`, `p₃`, `p₄` in `A_L̃`. The file shows that the elements entering the universal norm-descent lemma lie in the finite-stage unit group `U_L̃`.

## Main results

- `DegreeData.frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup`: with `nᵢ = d(σᵢ)` and `S(n, x)` the sum of the `φⁱ x` for `i < n`, the element `S(n₄, p₄) + S(n₁, p₁) − S(n₃, p₃)` lies in `U_L̃`.
- `DegreeData.frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup`: the three correction coefficients `p₄ − p₃`, `p₁ − p₃` and `p₃ − τ₁ p₃` lie in `U_L̃`, where `τ₁ = frobeniusActionRemainder φ σ₁`.

## Proof

Differences of two prime images, and `p₃ − q p₃` for any `q`, are finite-stage units by results of an earlier file on prime-unit differences. Using `n₃ = n₄ + n₁`, the alternating sum splits as `S(n₄, p₄ − p₃) + S(n₁, p₁ − φ^n₄ p₃)`, and Frobenius power sums preserve `U_L̃`.

## Watch for

The unit group here is the library's finite-stage unit group of `L̃`, made of elements that are units of some finite intermediate field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FiniteStageCorrections.lean`: the Lean file is the source byte for byte (SHA-256 `17339f960c75c4b5683a2a613521ba78fceb355080962fd1cd561fb1f400c65e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
