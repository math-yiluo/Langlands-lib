# The Frobenius power-sum relation

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusPowerSumRelation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A single identity in the abstract class field theory of the library, a step in the proof that the reciprocity map is multiplicative. It concerns a topological group `G`, a `G`-module `A`, an abstract field `K` with finite residue structure, a closed subgroup `L ≤ K` whose extension `L/K` is normal, and Frobenius elements `φ, σ₁, σ₂` of `L̃/K`. Put `σ₃ = σ₁σ₂` and `σ₄ = φ^(n₁) σ₂ φ^(-n₁)`, where `nᵢ` is the Frobenius exponent of `σᵢ`, and let `τᵢ = φ^(nᵢ) σᵢ⁻¹` be the action remainders.

## Main result

`frobeniusPowerSum_mul_action_sub`: let `p₁, p₃, p₄` be elements of `A` fixed by the fixed fields of `σ₁, σ₃, σ₄`, viewed in the invariants under the maximal unramified extension of `L`, and let `sᵢ` be the Frobenius power sum of `pᵢ` with respect to `φ` and `nᵢ`. Then `u = s₄ + s₁ − s₃` satisfies

`φ·u − u = (τ₄·p₄ − p₄) + (τ₁·p₁ − p₁) + (p₃ − (τ₄τ₁)·p₃)`.

## Proof

The action of `φ` is additive, and each power sum satisfies `φ·s − s = φⁿ·p − p` (`frobeniusPowerSum_action_sub`). On these fixed elements the remainder `τᵢ` acts as `φ^(nᵢ)` (`frobeniusActionRemainder_apply_fixedField`), and `τ₃ = τ₄τ₁` (`frobeniusActionRemainder_mul`).

## Watch for

The elements `p₁, p₃, p₄` are arbitrary fixed elements in this statement; their role as prime elements is only in the intended application. The identity is written for the left action of `Rep`, which is why `σ₄` is a conjugate by a power of `φ` and the product `τ₄τ₁` has this order.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusPowerSumRelation.lean`: the Lean file is the source byte for byte (SHA-256 `fdba4f0c04d9d84b47c9e5dfc9d9f435ad957227cad71e2b542c6c5ea38ed650`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
