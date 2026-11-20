# Averages over small sets of `Γ \ H` and the wave-packet bound

Module `Langlands.Global.ImaginaryAxisAveraging` (namespace
`Langlands.Global.ImaginaryAxis`) proves the measure-theoretic part of
the averaging step in the proof of Lapid's Proposition 6 (Task 5613). It
works for a second countable topological group `H` with a discrete subgroup
`Γ`, a measure `ν` on `H` invariant under left multiplication by `Γ` and
finite on compact sets, and the published quotient measure
`μ = LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν` on `Γ \ H`. Here
`Γ \ H` is `LeftCosetSpace Γ`, and `y.out` is a representative of `y`.
Applied with `H = G(𝔸)` and `Γ = G(F)`.

## Quotient lemmas

- `exists_mul_eq_out`, `apply_out_of_invariant`: the representative of the
  class of `g` is `c g` with `c ∈ Γ`, so a left `Γ`-invariant function `f`
  satisfies `f (mk g).out = f g`.
- `continuousOn_out_of_invariant`: if `(s, g) ↦ f s g` is continuous on
  `W × H` (`W` open) and left `Γ`-invariant in `g`, then
  `(s, y) ↦ f s y.out` is continuous on `W × (Γ \ H)`. The map
  `id × mk` is an open quotient map.
- `measurableSet_of_isOpen`, `quotient_opensMeasurableSpace`: open sets of
  `Γ \ H` are measurable.
- `measure_mk_image_pos`: `0 < μ (mk '' V)` for nonempty open `V` when `ν`
  is positive on open sets. The preimage of `mk '' V` is `Γ`-invariant, so a
  null intersection with the fundamental domain would make it null
  (`IsFundamentalDomain.measure_zero_of_invariant`).
- `measure_mk_image_le`: `μ (mk '' V) ≤ ν V` for open `V`. The preimage meets
  the fundamental domain inside `⋃ c, c • V ∩ s`, and
  `IsFundamentalDomain.measure_eq_tsum` sums these pieces to `ν V`.

## The averaged wave-packet bound

`setIntegral_norm_sq_average_le`. Let `k : ℝⁿ → H → ℂ` be continuous on
`T × H` for an open `T ⊆ ℝⁿ` and left `Γ`-invariant in `g` for `x ∈ T`, and
let `σ` be a measure on `ℝⁿ`, finite on compact sets. Suppose that for every
measurable bounded `c`, zero outside a compact `A ⊆ T`, the wave packet
`Θ_c(y) = ∫ c(x) k(x, y.out) dσ(x)` lies in `L²(μ)` with
`∫ |Θ_c|² dμ ≤ C ∫ |c|² dσ`. Then for every open `V ⊆ H` with compact
closure and every compact `A ⊆ T`,

`∫_A |∫_N k(x, y.out) dμ(y)|² dσ(x) ≤ max C 0 · μ(N)`, where `N = mk '' V`.

Proof. Put `K(x) = ∫_N k(x, y.out) dμ(y)`. It is continuous on `A` by
dominated convergence. The bound for `k` comes from compactness of
`A × closure V` and invariance. Take `c = conj K` on `A` and `0` elsewhere.
Fubini on `N × ℝⁿ` gives `∫_N Θ_c dμ = ∫ c K dσ = I := ∫_A |K|² dσ`. The
integrand is continuous on `(Γ \ H) × A` by `continuousOn_out_of_invariant`
and bounded on `N × A`. By Hölder's inequality with exponents `2, 2` on `N`,
`I² ≤ μ(N) ∫ |Θ_c|² dμ ≤ μ(N) · max C 0 · I`, hence `I ≤ max C 0 · μ(N)`.

This is the duality argument behind Lapid's comparison of `Θ_φ(x₀)` with
`‖Θ_φ‖_{L²}` (Lapid 2011, proof of Proposition 6, p.330). The wave packet
is tested against the indicator of `N` instead of being evaluated at the
point `x₀`, so continuity of `Θ_φ` near `x₀` is not needed.

## Shrinking neighbourhoods

- `shrinkingNhds g₀`: the filter `(𝓝 g₀).smallSets ⊓ 𝓟 {V | V open,
  g₀ ∈ V, closure V compact}` on `Set H`. `eventually_shrinkingNhds` gives
  eventual statements from statements about such `V` inside a neighbourhood
  of `g₀`. `shrinkingNhds_neBot` holds when `H` is locally compact and
  Hausdorff.
- `tendstoLocallyUniformlyOn_average`: for `h(s, g)` continuous on `W × H`
  (`W` open in a locally compact space) and left `Γ`-invariant in `g`, the
  averages `μ(mk '' V)⁻¹ ∫_{mk '' V} h(s, y.out) dμ(y)` tend to `h(s, g₀)`
  locally uniformly on `W` along `shrinkingNhds g₀`. Mathlib's
  `IsCompact.mem_uniformity_of_prod` gives uniform closeness of `h(s, g)` to
  `h(s, g₀)` for `s` in a compact set and `g` near `g₀`. The measure of
  `mk '' V` is positive and finite by the two lemmas above.

## Provenance

Internal. These are the measure-theoretic steps of Lapid's proof of
Proposition 6 (E. Lapid, *On Arthur's asymptotic inner product formula of
truncated Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §8, pp.329–330),
rearranged so that only averages over small sets of `G(F) \ G(𝔸)` occur.
