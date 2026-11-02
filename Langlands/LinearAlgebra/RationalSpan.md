# Rational spans of subsets of an abelian group and induced automorphisms

Author: Worker 1220.

This module is pure linear algebra. For an abelian group `M` and a subset `R ⊆ M`, it
defines the `ℚ`-span of the image of `R` in `ℚ ⊗[ℤ] M`. A group acting on `M` by
automorphisms that preserve `R` then acts `ℚ`-linearly on this span. It also identifies
`ℚ ⊗[ℤ] M` with `I → ℚ` when `M ≅ I → ℤ` with `I` finite.

It is a helper for task 6edfb074. Its planned use there, with `M = X*(S)` and `R` the
relative roots, is the span `ᵏV` of the relative roots of a maximal split torus `S` and
the action of `N_G(S)/C_G(S)` on it. That relative-roots module is not yet written. All
declarations are in the namespace `Langlands.LinearAlgebra.RationalSpan`.

## Source

- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - 25.16 (printed p.549, PDF p.565): `ᵏV` is the subspace of `X(S) ⊗ ℚ` spanned by the
    relative roots of `(G, S)`. The quotient `N_G(S)/C_G(S)` acts faithfully on `S` and is
    identified with its image in `GL_{ᵏV}`.
  - 25.17 (printed p.549, PDF p.565): the action of `N_G(S)` on `ᵏV` preserves the set
    `ᵏΦ` of relative roots.

## Provenance (derived)

Milne describes `ᵏV` and the action on it only for the character group of a maximal
split torus. This module isolates the linear algebra behind that construction, for an
arbitrary abelian group `M`, an arbitrary subset `R` and an arbitrary group `H` acting
on `M` while preserving `R`. Milne writes `X(S) ⊗ ℚ`. Here the tensor product is
`ℚ ⊗[ℤ] M`, with `ℚ` on the left so that Mathlib's base change `LinearEquiv.baseChange`
applies. The two are canonically isomorphic. Nothing in this module refers to group
schemes.

## Definitions

- `toRat : M →+ ℚ ⊗[ℤ] M`, the map `m ↦ 1 ⊗ m`.
- `ratSpan R : Submodule ℚ (ℚ ⊗[ℤ] M)`, the `ℚ`-span of `toRat '' R`.
- `ratAut : (M ≃ₗ[ℤ] M) →* ((ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M))`, which sends `e` to its base
  change `q ⊗ m ↦ q ⊗ e m` (Mathlib's `LinearEquiv.baseChange ℤ ℚ`). It is a monoid
  homomorphism because both sides agree on pure tensors
  (`TensorProduct.AlgebraTensorModule.ext`). Automorphisms of `M` are written as
  `ℤ`-linear equivalences `M ≃ₗ[ℤ] M` (with Mathlib's group structure on them,
  `f * g = g.trans f`). This Mathlib's `AddAut M` carries an additive group structure,
  so it would not serve as the target of a group homomorphism.
- `spanAut ρ R hρ : H →* (ratSpan R ≃ₗ[ℚ] ratSpan R)`, for `ρ : H →* (M ≃ₗ[ℤ] M)` and
  `hρ : ∀ h, Set.MapsTo (ρ h) R R`. Each `spanAut ρ R hρ h` is `ratAut (ρ h)`
  restricted to `ratSpan R` (`LinearEquiv.ofSubmodules`). The restriction is valid
  because `ratAut (ρ h)` maps `ratSpan R` onto `ratSpan (ρ h '' R) = ratSpan R`.
- `tensorEquivPi e : ℚ ⊗[ℤ] M ≃ₗ[ℚ] (I → ℚ)`, for `[Finite I]` and `e : M ≃+ (I → ℤ)`.
  It is the base change of `e` followed by Mathlib's `TensorProduct.piScalarRight`
  (`ℚ ⊗[ℤ] (I → ℤ) ≃ I → ℚ`).

## Lemmas

- `toRat_apply`: `toRat m = 1 ⊗ m` (by definition).
- `toRat_mem_ratSpan`: `m ∈ R` gives `toRat m ∈ ratSpan R`.
- `ratAut_tmul`: `ratAut e (q ⊗ m) = q ⊗ e m`. `ratAut_toRat`:
  `ratAut e (toRat m) = toRat (e m)`. Both hold by definition.
- `map_ratSpan`: the image of `ratSpan R` under `ratAut e` is `ratSpan (e '' R)`. The
  proof uses `Submodule.map_span` and composition of images.
- `image_eq_of_mapsTo`: if every `ρ h` maps `R` into `R`, then `ρ h '' R = R`. The
  reverse inclusion uses `ρ h⁻¹`.
- `coe_spanAut_apply`: as an element of `ℚ ⊗[ℤ] M`, `spanAut ρ R hρ h x` is
  `ratAut (ρ h) x`.
- `spanAut_eq_one_of_eq_one`: if `ρ h = 1`, then `spanAut ρ R hρ h = 1`. So the action
  on the span factors through the image of `ρ`. In the planned use, this is how the
  action of `N(k)` factors through `N(k)/Z(k)`.
- `tensorEquivPi_tmul`: `tensorEquivPi e (q ⊗ m) = fun j => (e m j : ℚ) * q`.
  `tensorEquivPi_toRat`: `tensorEquivPi e (toRat m) = fun j => (e m j : ℚ)`. Both are
  proved by `simp` with `TensorProduct.piScalarRight_apply`.
- `toRat_injective`: if `M ≃+ (I → ℤ)` for some finite `I`, then `toRat` is injective.
  Apply `tensorEquivPi e`, compare coordinates, and cancel the cast `ℤ → ℚ`.
