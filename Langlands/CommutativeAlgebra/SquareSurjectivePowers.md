# Surjectivity modulo the square of an ideal propagates to all powers

This internal module contains a standard graded Nakayama-type argument. Let
`φ : S →+* A` be a ring homomorphism, with `S : Type u` and `A : Type v`
commutative, and let `u` be an ideal of `A`. Write `φ⁻¹ u` for `u.comap φ`.

- `map_mem_pow`: if `s ∈ (φ⁻¹ u) ^ k`, then `φ s ∈ u ^ k`.
- `exists_mem_pow_sub_mem_pow_succ`: assume every `a : A` has some `s` with
  `a - φ s ∈ u ^ 2`. Then for every `k ≥ 1` and every `t ∈ u ^ k` there is
  `s ∈ (φ⁻¹ u) ^ k` with `t - φ s ∈ u ^ (k + 1)`.
- `exists_sub_mem_pow`: under the same hypothesis, for every `k` and every `a`
  there is `s` with `a - φ s ∈ u ^ k`.

For `k = 1`, take `s` with `t - φ s ∈ u ^ 2`. Then `φ s ∈ u`, so `s ∈ φ⁻¹ u`.
For the inductive step, `u ^ (k + 1) = u ^ k * u` is handled by multiplicative
induction. For a product `a * b`, write `a = φ s₁ + e₁` and `b = φ s₂ + e₂` with
`e₁ ∈ u ^ (k + 1)` and `e₂ ∈ u ^ 2`. Expanding,
`a * b - φ (s₁ * s₂) = φ s₁ * e₂ + e₁ * φ s₂ + e₁ * e₂ ∈ u ^ (k + 2)`. Sums are
handled additively. The last statement follows by induction on `k`, applying the
graded statement to the current error term.
