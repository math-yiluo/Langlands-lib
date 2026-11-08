# Trace compatibility of norm-equivariant bilinear maps

This module is linear algebra over fields and uses only Mathlib. It proves one result,
`add_eq_trace_mul`. Let `B : E × E → E` be a `k`-bilinear map that is equivariant for a
"norm" `c ↦ c σ(c)` on a set `C`. If the products of embeddings separate the right pairs
on `C`, then `B` satisfies the trace identity
`B (f x) y + B x (f y) = (f + σ f) B x y`.

The intended use is the unitary root groups of a quasi-split group. There `E` is the field
of an absolute root `β`, `σ` is the conjugation of `E` over the field of `β + β'`, and `B` is
the bilinear part of the Heisenberg law of the root group, with `c` running over the values of
`β` on rational points of the torus. In that setting `hnorm` is the scaling law of the root
group, and `hsep` has to come from the Galois action on roots. This module does not mention
roots or groups and makes none of these identifications.

Provenance: internal. The argument is the standard use of Dedekind's linear independence of
embeddings (Mathlib's `linearIndependent_algHom_toLinearMap`). It is not taken from a
specific source.

## Setting

All declarations live in namespace `Langlands.Algebra.NormEquivariantBilinear`. The variables
are fields `k E L : Type*` with `[Algebra k E] [Algebra k L]`. Embeddings are `k`-algebra
maps `E →ₐ[k] L`, and every statement assumes `[Fintype (E →ₐ[k] L)]`. All declarations
except `coeff_eq_zero` also assume `[FiniteDimensional k E]` and

`hcard : Nat.card (E →ₐ[k] L) = finrank k E`,

that is, `E` has as many embeddings into `L` as its degree. When `E / k` is separable and the
minimal polynomials of `E` split in `L`, this is Mathlib's `AlgHom.natCard_of_splits`.

## Declarations

- `coeff_eq_zero`: let `a : (E →ₐ[k] L) → (E →ₐ[k] L) → L`. If
  `∑ τ, ∑ ρ, a τ ρ * τ x * ρ y = 0` for all `x y : E`, then every `a τ ρ` is zero.
  Proof. Fix `y`. Then the function `x ↦ ∑ τ, (∑ ρ, a τ ρ * ρ y) * τ x` vanishes. So by linear
  independence of the embeddings, `∑ ρ, a τ ρ * ρ y = 0` for every `τ`. Linear independence
  applied once more, now in `y`, gives `a τ ρ = 0`.
- `embeddingBasis hcard : Basis (E →ₐ[k] L) L (E →ₗ[k] L)`: the embeddings, viewed as
  `k`-linear maps, form an `L`-basis of the `k`-linear maps `E → L`. They are linearly
  independent, and their number equals `finrank L (E →ₗ[k] L) = finrank k E`
  (`Module.finrank_linearMap_self`). The basis is
  `basisOfLinearIndependentOfCardEqFinrank'`.
- `embeddingBasis_apply`: `embeddingBasis hcard τ = τ.toLinearMap`.
- `linearMap_eq_sum`: every `k`-linear map `φ : E →ₗ[k] L` satisfies
  `φ x = ∑ τ, (embeddingBasis hcard).repr φ τ * τ x`.
- `exists_coeff`: every `k`-bilinear map `B : E →ₗ[k] E →ₗ[k] L` has coefficients `a` with
  `B x y = ∑ τ, ∑ ρ, a τ ρ * τ x * ρ y`. Proof. Expand `B x` in the basis. For each `ρ`, the
  `ρ`-coordinate of `B x` is `k`-linear in `x`, so expand it in the basis too. Then exchange
  the two sums.
- `add_eq_trace_mul`: the main theorem. Its data are `σ : E →ₐ[k] E`, a set `C : Set E`, and
  `B : E →ₗ[k] E →ₗ[k] E`. Its hypotheses are `hcard` and:
  - `hnorm`: `B (c * x) (c * y) = c * σ c * B x y` for all `c ∈ C` and `x y : E`;
  - `hsep`: for all embeddings `π τ ρ`, if `τ c * ρ c = π c * π (σ c)` for every `c ∈ C`, then
    `τ = π ∧ ρ = π.comp σ` or `τ = π.comp σ ∧ ρ = π`.

  The conclusion is `B (f * x) y + B x (f * y) = (f + σ f) * B x y` for all `f x y : E`.

  Proof. `hcard` and `0 < finrank k E` give an embedding `π`. Since `π` is injective, it
  suffices to prove the identity after applying `π`. By `exists_coeff`, write
  `π (B x y) = ∑ τ, ∑ ρ, a τ ρ * τ x * ρ y`. For `c ∈ C`, apply this to `B (c x) (c y)` and
  use `hnorm`. Subtracting the two expansions gives
  `∑ τ, ∑ ρ, a τ ρ * (τ c * ρ c - π c * π (σ c)) * τ x * ρ y = 0`. So by `coeff_eq_zero`,
  `a τ ρ * (τ c * ρ c - π c * π (σ c)) = 0`. Hence, whenever `a τ ρ ≠ 0`, the pair `(τ, ρ)`
  satisfies the premise of `hsep`. It is therefore `(π, π σ)` or `(π σ, π)`, and in both
  cases `τ f + ρ f = π (f + σ f)`. So
  `a τ ρ * (τ f + ρ f) = a τ ρ * π (f + σ f)` for every pair. Expand
  `π (B (f x) y + B x (f y))` and `π ((f + σ f) * B x y)` with the coefficients `a`. They
  agree term by term, by this identity.

## Scope

The module proves no instance of `hnorm` or `hsep`, and it does not build `B`, `σ` or `C`
from a group.
