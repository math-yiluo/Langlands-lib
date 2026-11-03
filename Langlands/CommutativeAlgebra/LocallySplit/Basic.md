# Locally split modules

This module defines one predicate, `Langlands.CommutativeAlgebra.LocallySplit`. It is used in
the proof of `Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project,
Tag 05FT). It imports only `Mathlib.LinearAlgebra.Pi`, which supplies the module structure on
`Fin r → R`.

## Definition

Let `R` be a commutative ring and `M` an `R`-module. Then `LocallySplit R M` means: for every
`n : ℕ` and every tuple `x : Fin n → M` there are `r : ℕ`, an `R`-linear map
`φ : M →ₗ[R] (Fin r → R)` and elements `y : Fin r → M` such that

  `∑ j, φ (x i) j • y j = x i` for every `i`.

Equivalently, the endomorphism `m ↦ ∑ j, φ m j • y j` of `M`, which factors through the finite
free module `R^r`, fixes each `x i`. So the identity of `M` agrees, on any given finite set of
elements, with an endomorphism that factors through a finite free module.

## Provenance

The definition is internal to this project. Worker 281 proposed it as the interface between the
geometric part of the 05FT proof and the module-theoretic part, and Worker 928 wrote this file.
In the literature the condition is known as "locally projective" (Zimmermann-Huisgen). It is
used here only through the projectivity criterion
`Langlands.CommutativeAlgebra.projective_of_locallySplit_baseChange` in
`Langlands.CommutativeAlgebra.LocallySplit.Projective`. This file claims no other properties of
the predicate.
