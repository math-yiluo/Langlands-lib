# Divisibility at a point of the imaginary axis

Module `Langlands.Global.ImaginaryAxisLocalDivision` (namespace
`Langlands.Global.ImaginaryAxis`) proves the abstract core of Lapid's
Proposition 6 (Task 5613). It has no automorphic input.

## Helpers

- `setIntegral_comp_add_left`: `∫_A f(x₀ + x) dx = ∫_{x₀ + A} f(x) dx` for
  Lebesgue measure on `ℝⁿ`.
- `imaginarySlice_add`: `(i x₀ + i x)_j = imaginarySlice (x₀ + x)`.
- `continuous_imaginarySlice`.

## Local divisibility

`exists_local_division`. The data:

- a group `H` (second countable, locally compact, Hausdorff) with a discrete
  subgroup `Γ` and a measure `ν` that is `Γ`-invariant, positive on open
  sets and finite on compact sets. Let `μ` be the quotient measure on
  `Γ \ H`;
- a measure `c · vol` on `ℝⁿ` with `0 < c < ∞`;
- a point `x₀ ∈ ℝⁿ`, so `s₀ = i x₀`, and an open `W ∋ s₀` in `ℂⁿ`;
- `h : ℂⁿ → H → ℂ`, continuous on `W × H`, holomorphic in `s ∈ W`, left
  `Γ`-invariant;
- a continuous `Q : ℂⁿ → ℂ`, and `k : ℝⁿ → H → ℂ` with `k(x, g) =
  h(i x, g) / Q(i x)` whenever `i x ∈ W` and `Q(i x) ≠ 0`;
- the wave-packet bound `hwave`. For bounded measurable `c'` vanishing
  outside a compact subset of `{x | i x ∈ W, Q(i x) ≠ 0}`, the packet
  `∫ c'(x) k(x, y.out) d(c · vol)` is in `L²(μ)` with
  `‖·‖² ≤ C ∫ |c'|²`;
- a radius `ρ` with `s₀ + i x ∈ W` for `|x| < ρ`;
- `hdiv`: the division lemma in the form proved by Worker 757 for products
  of real root forms (module `RealHyperplaneDivision`, Task 5613). It gives
  an open `W' ∋ s₀`, `W' ⊆ W`, depending only on these data. Let
  `H_V → H_∞` be a locally uniform limit on `W` of holomorphic functions
  along a nontrivial filter, and suppose `H_V / Q` has eventually bounded
  `L²` norms on compact subsets of the slice ball avoiding `Q = 0`. Then
  `H_∞ = Q · H'` on `W'` with `H'` holomorphic.

Conclusion: there is an open `W' ∋ s₀`, `W' ⊆ W`, such that for every
`g₀ ∈ H` some `H'` holomorphic on `W'` satisfies `h(s, g₀) = Q(s) H'(s)` on
`W'`. The neighbourhood does not depend on `g₀`.

Proof. Take `W'` from `hdiv` and fix `g₀`. Apply `hdiv` along the filter
`shrinkingNhds g₀` to the averages
`H_V(s) = μ(N)⁻¹ ∫_N h(s, y.out) dμ(y)`, `N = mk '' V`.

- Holomorphy of `H_V`: Worker 757's
  `Langlands.Analysis.SeveralComplex.differentiableOn_integral_of_bounded`,
  applied to `1_N · h(s, ·.out)` for the finite measure `μ|_N`. The bound on
  compact sets comes from continuity of `h` on `K × closure V` and
  invariance.
- Convergence `H_V → h(·, g₀)`: `tendstoLocallyUniformlyOn_average`.
- `L²` bounds: for `x` in a compact `A ⊆ ball 0 ρ` with `Q(s₀ + i x) ≠ 0`,
  `H_V(s₀ + i x) / Q(s₀ + i x) = μ(N)⁻¹ K(x₀ + x)`, with
  `K(x') = ∫_N k(x', y.out) dμ(y)`. After the translation `x' = x₀ + x` and
  the change from `c · vol` to `vol`, `setIntegral_norm_sq_average_le`
  bounds the integral by `μ(N)⁻² c⁻¹ max C 0 · μ(N)`. This bound does not
  depend on `A`.

## Provenance

Internal. Lapid (2011, §8, proof of Proposition 6, pp.329–330; registered
as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`) bounds
`Θ_φ(x₀)` against `‖Θ_φ‖_{L²}` near a generic point of a singular
hyperplane, using continuity of `E*(x, λ)` in `x`. This module replaces
that pointwise comparison by averages over shrinking neighbourhoods of
`x₀` in `Γ \ H` and a division lemma for their limit. So no generic point,
leading coefficient or asymptotic in `η` is needed, and the conclusion
holds at every `g₀`.
