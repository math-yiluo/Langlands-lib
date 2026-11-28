# Cancellation of a unit summand in `2 × 2` matrices

Module: `Langlands.Algebra.CentralSimple.LandherrCancellation`.

Let `B` be an algebra over a commutative ring `F` with an involution
`τ : FirstKindInvolution F B` (an involutive `F`-linear anti-automorphism), and let
`τ.matrix (Fin 2)` be the induced involution `Z ↦ ᵗτ(Z)` of `M₂(B)`.

- `matrix_fin_two` writes `τ.matrix (Fin 2) !![a, b; c, d] = !![τ a, τ c; τ b, τ d]`.
- In `quasiReflection_mul`, set `S = u₀ τ(u₀) + u₁ τ(u₁)` and `Q = 1 - ᵗτ(u) λ u`,
  with entries `δᵢⱼ - τ(uᵢ) λ uⱼ`. If `λ + τ λ = λ S τ(λ)`, then `Q ᵗτ(Q) = 1`.
  The proof expands the four entries of
  `1 - Q ᵗτ(Q)` as `τ(uᵢ) (λ + τ λ - λ S τ λ) uⱼ`, which vanish by the hypothesis.
- `exists_eq_mul_of_diag`: if `Z ᵗτ(Z) = diag(y, 1)` and `μ ∈ B` is central with
  `μ τ(μ) = 1` and `μ - Z₁₁` a unit `p`, then `y = a τ(a)` for some `a ∈ B`.

## Proof of `exists_eq_mul_of_diag`

Write `c = Z₁₀`, `d = Z₁₁`; the `(1,1)` entry of `Z ᵗτ(Z)` gives `c τ(c) + d τ(d) = 1`.
Put `u = (c, d - μ)`, `β = p τ(μ) = 1 - d τ(μ)` and `λ = μ p⁻¹`, so that `β λ = λ β = 1`,
`c τ(u₀) + d τ(u₁) = β` and `u₀ τ(u₀) + u₁ τ(u₁) = β + τ β`. These identities give the
hypothesis of `quasiReflection_mul`, so `Q ᵗτ(Q) = 1` for `Q = 1 - ᵗτ(u) λ u`.
Thus `W = Z Q` satisfies `W ᵗτ(W) = diag(y, 1)`. A computation of the second row gives `W₁₀ = 0` and
`W₁₁ = μ`. The `(0,1)` entry of `W ᵗτ(W)` then reads `W₀₁ τ(μ) = 0`, so `W₀₁ = 0` because
`τ(μ) μ = 1`, and the `(0,0)` entry reads `W₀₀ τ(W₀₀) = y`.

## Provenance

The quasi-reflection `Q` moves the second row of `Z` to `(0, μ)`. For a factorization
by an invertible `Z`, this is the Witt cancellation step for the hermitian isometry
`⟨y⟩ ⊥ ⟨1⟩ ≅ ⟨1⟩ ⊥ ⟨1⟩`. In the Library's proof of Landherr's theorem,
`exists_eq_mul_of_diag_unit` (module `Langlands.Algebra.CentralSimple.LandherrFinish`)
uses the calculation to descend a solution in `M₂(B)` to a solution in `B`.
