# The class-function form of the Artin conductor

Worker 4803 wrote this supporting module of
`SpectralConductor.spectralConductorRankOneReduction`.

## Declarations

- `finrank_fixedVectors`: for a finite group `G`, a finite-dimensional complex
  representation `ρ` and a subgroup `H`,
  `dim V^H = |H|^{-1} Σ_{g ∈ H} tr ρ(g)`.
- `weightedCodimension_eq`: for subgroups `H, G₀`,
  `(|H| / |G₀|) · codim V^H = |G₀|^{-1} Σ_{g ∈ H} (dim V - tr ρ(g))`.
- `lowerCount R G b g` is the number of indices `i < b` with `g` in the lower
  ramification group `lowerGroup R G i`.
- `artinConductor_eq_classSum`: for a finite group acting faithfully on a Noetherian
  local ring `R`, and any `b` beyond which the lower groups are trivial, the Library's
  Artin expression satisfies
  `a(ρ) = |G₀|^{-1} Σ_{g ∈ G} m(g) (dim V - tr ρ(g))`, with `m = lowerCount R G b`.

## Proofs

`finrank_fixedVectors`: the Library's `fixedVectors ρ H` is Mathlib's invariant
submodule of the restriction of `ρ` to `H`. Mathlib's `averageMap` is a projection
onto it (`Representation.isProj_averageMap`), so its trace is the dimension
(`LinearMap.IsProj.trace`). Expanding the average gives the trace formula; the sum
over `H` is rewritten as a sum over `G` with an indicator.

`weightedCodimension_eq`: substitute `finrank_fixedVectors` into
`codim V^H = dim V - dim V^H` and clear denominators.

`artinConductor_eq_classSum`: `Ramification.artinConductor_eq_sum_range` writes the
Artin expression as `Σ_{i<b}` of the Library's `conductorTerm`, which is the weighted
codimension above with `H = G_i`. Then exchange the two sums.

## Source

Serre, *Local Fields* (1979), VI §2, Proposition 2 and Corollary 1', printed pp. 100–101
(PDF pp. 107–108). The Library defines the Artin expression as
`Σ_i (g_i / g_0) codim V^{G_i}`, the formula of Corollary 1'. This module returns to
Serre's class-function form `(1/g_0) Σ_s i_G(s) (χ(1) - χ(s))`, where
`i_G(s) = m(s)` counts the lower groups containing `s`.
