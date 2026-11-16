# A `K`-type of a `(𝔤𝔩_n(ℝ), O(n))`-module as matrix data

Module: `Langlands.Representation.Archimedean.RealSubquotientKType` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is a helper module for the proof of `RealPrincipalSeriesSubquotientStatement`; see
`RealPrincipalSeriesSubquotientProof.md`. It turns a nonzero vector of a
`(𝔤𝔩_n(ℝ), O(n))`-module into the matrix data that the other helper modules use. This data is a
continuous matrix representation `τ` of `O(n)`, its derivative `D`, and a nonzero `K`-intertwiner
`T₀` from `τ`. The representation `τ` need not be irreducible.

- `transpose_eq_neg_of_curve`: let `γ` be a curve in `O(n)` with `γ(0) = 1` whose entries have
  derivative `X` at `0`. Then `Xᵀ = -X`. Differentiate `γ(t)ᵀ γ(t) = 1`.
- `skewPart_eq_self`: `RealJacquetFrobenius.skewPart Y = Y` for antisymmetric `Y`.
- `exists_ktype`: let `V` be a nontrivial `(𝔤𝔩_n(ℝ), O(n))`-module (`IsRealGKModule n ρ π`).
  Then there are `d > 0`, `τ : O(n) →* Mat_d(ℂ)`, `D : 𝔤𝔩_n(ℝ) →ₗ[ℝ] Mat_d(ℂ)` and
  `T₀ : ℂ^d →ₗ V` with `τ` continuous, `IsTypeDerivative τ D`,
  `T₀ ∈ gkIntertwiners ρ d τ` and `T₀ ≠ 0`. Construction: pick `v₀ ≠ 0`. Its orbit span
  `F₀ = FiniteVectors.orbitSpan ρ v₀` is finite-dimensional and `O(n)`-stable. Choose a basis
  `bF` of `F₀` and linear functionals `ℓᵢ` on `V` extending its coordinates. Set
  `τ(k)ᵢⱼ = ℓᵢ(ρ(k) bFⱼ)`, `D(X)ᵢⱼ = ℓᵢ(π(1 ⊗ skewPart X) bFⱼ)` and `T₀ x = ∑ᵢ xᵢ bFᵢ`.
  Continuity of `τ` comes from the continuity clause of `IsRealGKModule`. The derivative
  property comes from its derivative clause together with `transpose_eq_neg_of_curve` and
  `skewPart_eq_self`.
