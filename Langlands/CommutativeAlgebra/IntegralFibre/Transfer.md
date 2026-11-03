# From a Noetherian model to local splitting

This module is part of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
It transfers the hypotheses of `locallySplit_of_model` from a `B`-algebra `S` to a Noetherian
model of it.

## Definitions

`modelMap e : S₀ →+* S`, for `e : B ⊗[R₀] S₀ ≃ₐ[B] S`, is `s ↦ e (1 ⊗ s)`.

## Statements

- `LocallySplit.of_linearEquiv`: local splitting transfers along linear equivalences.
- `tpow_modelMap`, `modelMap_algebraMap`, `ker_le_comap_modelMap`: compatibilities of `modelMap`
  with monomials, scalars and kernels of the sections. Here `σ : S →ₐ[B] B` and
  `σ₀ : S₀ →ₐ[R₀] R₀` satisfy `algebraMap (σ₀ s) = σ (modelMap e s)`.
- `theta_injective_of_model`: suppose `algebraMap R₀ B` is injective and every `theta σ t k` is
  injective. Then every `theta σ₀ t₀ k` is injective.
- `smulInjOn_of_isDomain`: suppose `P.ResidueField ⊗[B] S` is a domain for a prime `P` of `B`.
  Then multiplication by any `u` with `σ₀ u = 1` is injective on `S₀ ⊗[R₀] P.ResidueField`.
- `locallySplit_of_noetherianModel`: suppose `R₀` and `S₀` are Noetherian, `S₀` is flat, the
  map `R₀ → B` is injective, and `ker σ₀ ≤ span (range t₀) ⊔ (ker σ₀)^2`. Suppose further that
  every `theta σ t k` is injective and that every fibre `P.ResidueField ⊗[B] S` is a domain.
  Then `LocallySplit B S`.

## Proofs

For injectivity, `modelMap` induces `S₀/J₀^k → S/J^k`. Composed with `theta σ₀ t₀ k`, it equals
`theta σ t k` composed with the injective map `(Mon →₀ R₀) → (Mon →₀ B)`.

For the fibres, the ring isomorphism
`S₀ ⊗[R₀] κ(P) ≃ κ(P) ⊗[R₀] S₀ ≃ κ(P) ⊗[B] (B ⊗[R₀] S₀) ≃ κ(P) ⊗[B] S` carries `u ⊗ 1` to
`1 ⊗ modelMap u`. That element is nonzero, because the map `κ(P) ⊗ S → κ(P)` induced by `σ`
sends it to `1`. Multiplication by a nonzero element of a domain is injective.

The final theorem combines these facts with `theta_surjective` and `locallySplit_of_model`, and
transports the result along `e`.

## Provenance

This is internal to the 05FT proof, written by Worker 281.
