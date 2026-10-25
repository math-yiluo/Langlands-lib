# The noetherian model step of the Čech criterion

Authors: Worker 299 and Worker 424. Worker 299 authored the proof;
Worker 424 adapted its module dependencies for separate prerequisite
publication and rechecked the complete proof. This helper module supports the proof of
`Langlands.Algebra.SmoothEqualizerFibreCriterion`. It contains internal
formal deductions from Mathlib and from the companion module
`Langlands.Algebra.CechEqualizer.Good`; no literature result is formalized
here.

## Associated primes of an algebra

`exists_comap_eq_of_mem_associatedPrimes`: let `A₀` be noetherian and `A` an
`A₀`-algebra. Every associated prime `q` of `A`, viewed as an `A₀`-module,
is the contraction of a prime ideal `P` of `A`. Write
`q = ann_{A₀}(a)` and let `I = ann_A(a)`. Then the contraction of `I` to
`A₀` is `q`, so `q` is a minimal prime over the contraction of `I`;
Mathlib's `Ideal.exists_comap_eq_of_mem_minimalPrimes` gives a prime
`P ⊇ I` of `A` contracting to `q`.

## Residue fields of `A` are good

The setting: `A₀ → A`, `A`-algebras `C₀`, `C₁` with `δ₁ δ₂ : C₀ →ₐ[A] C₁`,
`A₀`-algebras `C₀'`, `C₁'` with an `A₀`-linear `d : C₀' → C₁'`, and
`A`-linear maps `e₀ : A ⊗[A₀] C₀' ≃ C₀` (an isomorphism) and
`e₁ : A ⊗[A₀] C₁' → C₁` such that `e₁ ∘ (A ⊗ d) = (δ₁ - δ₂) ∘ e₀`
(hypothesis `hde`).

`good_residueField`: if `e₀ (1 ⊗ 1) = 1` and, for the prime `P` of `A`,
every element of `κ(P) ⊗[A] C₀` equalized by `id ⊗ δ₁` and `id ⊗ δ₂` is a
scalar, then `κ(P)` is good for `d` (as an `A₀`-module). The proof
identifies `κ(P) ⊗[A₀] C₀'` with `κ(P) ⊗[A] C₀` through
`κ(P) ⊗[A₀] C₀' ≅ κ(P) ⊗[A] (A ⊗[A₀] C₀')`
(`TensorProduct.AlgebraTensorModule.cancelBaseChange`) followed by `e₀`, and
similarly for `C₁'` with `e₁`. Under these maps `κ(P) ⊗ d` becomes
`(id ⊗ δ₁) - (id ⊗ δ₂)`, so a kernel element maps to an equalized element
`k ⊗ 1`; injectivity of the identification gives the preimage `k ⊗ 1`.
Only the isomorphism `e₀` needs to be injective here.

## The model criterion

`mem_range_of_model`: assume moreover that `A₀` is noetherian, `C₀'` is
faithfully flat and `C₁'` flat over `A₀`, `d 1 = 0`,
`e₀ (a ⊗ 1) = algebraMap A C₀ a` for all `a`, `e₁` is injective, and the
fibre hypothesis holds at every prime of `A`. Then every `c : C₀` with
`δ₁ c = δ₂ c` lies in the range of `algebraMap A C₀`.

Proof. By the noetherian core `good_of_associatedPrimes`, the `A₀`-module
`A` is good once `κ(q)` is good for each associated prime `q` of `A`. Such a
`q` is the contraction of a prime `P` of `A`. `κ(P)` is good by
`good_residueField`, and the residue-field map `κ(q) → κ(P)`
(`Ideal.ResidueField.mapₐ`) is an injective `A₀`-linear map, so `κ(q)` is
good by `good_of_injective`. Now `e₀⁻¹ c ∈ A ⊗[A₀] C₀'` lies in the kernel of
`A ⊗ d`: applying the injective map `e₁` gives `δ₁ c - δ₂ c = 0`. Goodness of
`A` gives `a` with `a ⊗ 1 = e₀⁻¹ c`, so `c = e₀ (a ⊗ 1) = algebraMap A C₀ a`.

This proof does not use a separate faithful-flatness descent argument: the
residue-field transfer from `κ(P)` to `κ(q)` is by injectivity, which is
enough because good modules are closed under submodules.
