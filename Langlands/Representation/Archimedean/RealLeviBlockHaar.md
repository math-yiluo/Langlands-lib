# The Haar measure of a block orthogonal subgroup of `O(N)`

Lean module: `Langlands.Representation.Archimedean.RealLeviBlockHaar`.

This is a
helper module of the proof of `Langlands.Archimedean.RealLeviParabolicIntegrationStatement` (see
`RealLeviParabolicIntegration.md`). It states no proposition for publication; it proves lemmas
only. The content is internal and follows no literature source; it uses Mathlib's uniqueness of
Haar probability measures on compact groups. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealLeviBlockHaar`. `dg`, `dgGL`, `dgLinL` and `dgLinR` are from the
helper module `RealLeviTwoBlock`, and `clR` is from the helper module `RealLeviChartIntegrable`
(`clR cl r = cl (a + r)`). `O(n)` is `unitaryCompact ℝ n` with the Borel σ-algebra
`measurableSpaceK` and the Haar probability measure `haarK n` (Library
`RealPrincipalSeriesDuality`).

## Second countability

- `secondCountableTopology_GL n`: `GL_n(ℝ)` is second countable. Its topology is induced from
  `M_n(ℝ) × M_n(ℝ)ᵐᵒᵖ` by `Units.embedProduct`.
- `secondCountableTopology_O n`: `O(n)` is second countable.

Both are theorems, not global instances; later modules make them local instances. They are
needed for Mathlib's results on products of Borel spaces and on Haar measures.

## The block orthogonal subgroup (section `Group`)

For a block function `cl : Fin N → ι` into a linear order (positions `p` and `q` lie in the same
block if `cl p = cl q`):

- `Kc cl` is the subgroup of `GL_N(ℝ)` of the orthogonal matrices `g` with `g_{pq} = 0` whenever
  `cl p ≠ cl q`. The inverse of such a `g` is `gᵀ`, which has the same zero pattern.
  `mem_unitaryCompact_of_mem_Kc`: `Kc cl` lies in `O(N)`.
- `isClosed_Kc`, `isCompact_Kc`: `Kc cl` is closed in `GL_N(ℝ)` and compact. The instances
  `compactSpace_Kc`, `measurableSpace_Kc` (Borel), `borelSpace_Kc` and `secondCountableTopology_Kc`
  are global.
- `μc cl` is Mathlib's `Measure.haarMeasure` on `Kc cl` normalized on the whole group. It is a Haar
  measure (`isHaarMeasure_μc`) and a probability measure (`isProbabilityMeasure_μc`).
- `eq_μc`: every Haar probability measure on `Kc cl` is `μc cl`
  (`Measure.isHaarMeasure_eq_of_isProbabilityMeasure`).

## Continuity of the block embedding (section `Continuity`)

- `continuous_dg`: `(A, B) ↦ diag(A, B)` is continuous; it is the sum of the linear maps `dgLinL`
  and `dgLinR`.
- `continuous_dgGL`: `dgGL : GL_a(ℝ) × GL_M(ℝ) → GL_{a+M}(ℝ)` is continuous. The underlying
  matrices of `dgGL (g, h)` and of its inverse are `diag(g, h)` and `diag(g⁻¹, h⁻¹)`.

## The first-block decomposition (section `Peel`)

Here `cl : Fin (a + M) → ι` is constant `c₀` on the first `a` positions (hypothesis `h1`), and
`h2` says that `cl > c₀` on the last `M` positions.

- `dgGL_mem_Kc` (needs `h1`): `diag(k₁, k₂) ∈ Kc cl` for `k₁ ∈ O(a)` and `k₂ ∈ Kc (clR cl)`.
- `dgK h1 : O(a) × Kc (clR cl) →* Kc cl` is `(k₁, k₂) ↦ diag(k₁, k₂)` (`dgK_val`), and
  `continuous_dgK` says that it is continuous.
- `surjective_dgK` (needs `h2`): every `k ∈ Kc cl` is `diag(A, B)`. The entries of `k` between the
  first `a` and the last `M` positions vanish, because these positions lie in different blocks.
  From `k kᵀ = 1` we get `A Aᵀ = 1` and `B Bᵀ = 1`, and `B` has the zero pattern of `clR cl`.
- `map_dgK`: `μc cl` is the image of `haarK a ⊗ μc (clR cl)` under `dgK h1`. The product of the
  two Haar probability measures is a Haar measure on `O(a) × Kc (clR cl)`. Its image under a
  continuous surjective homomorphism is a Haar measure
  (`Measure.isHaarMeasure_map_of_isFiniteMeasure`), and it is a probability measure, so `eq_μc`
  applies.
- `integral_Kc_eq`: for continuous `f : Kc cl → ℂ`,
  `∫_{Kc cl} f dμc cl = ∫_{O(a)} ∫_{Kc (clR cl)} f(diag(k₁, k₂)) dk₂ dk₁`. This is `map_dgK`, the
  change of variables `integral_map`, and Fubini (`integral_prod`). The integrand
  `f ∘ dgK h1` is continuous on a compact space, so it has compact support and is integrable
  (`Continuous.integrable_of_hasCompactSupport`).
