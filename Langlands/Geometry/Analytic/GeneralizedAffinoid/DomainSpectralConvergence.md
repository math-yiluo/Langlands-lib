# Spectral convergence of factorizations through affinoid domains

Author: Worker 976.

This internal module extends the Library's `SpectralConvergesOn` from
`AffinoidPushoutSpectralTests` from algebra maps to their factorizations
through affinoid domains. It works over a complete ultrametric normed field
`K : Type u`, with presented affinoid algebras `A` and `B` and a parameter type
`T : Type v`, where the universes are independent.

Fix a filter `l` on `T`, maps `φ : T → BoundedAlgHom K A B`, and a limit map
`ψ`. The standing hypothesis `h : ∀ a, SpectralConvergesOn l φ ψ a` says the
following. For every section `a` and every `ε > 0`, eventually along `l`, every
point `x` of the spectrum of `B` satisfies `x (φ t a - ψ a) ≤ ε`.

## Elementary estimates

- `spectrum_apply_map_le`: a spectrum point of `B` evaluated on `f a` is at
  most `‖a‖`, for any bounded map `f`.
- `spectrum_sub_le_max`: the nonarchimedean inequality
  `x (a - b) ≤ max (x a) (x b)`.
- `SpectralConvergesOn.postcomp`: postcomposition with a bounded map
  `β : B → C` preserves spectral convergence. A point of `C` pulls back to a
  point of `B`.

## Weighted rational charts

For `d : RationalChart K A`, write `b` for its denominator class and `f_j` for
its numerator classes. The locus is `{y | ∀ j, y f_j ≤ r_j * y b}`.

- `RationalChart.comap_mem_locus_of_spectral_close` and
  `comap_mem_locus_iff_of_spectral_close`: suppose `ε` is a lower bound of the
  denominator on the locus. Suppose further `x (f b - g b) < ε` and
  `x (f f_j - g f_j) ≤ r_j * ε` at a point `x` of `B`. Then `x` pulls back into
  the locus along `f` if and only if it does along `g`. The denominator values
  agree by the strict ultrametric inequality. The numerator bound follows from
  the ultrametric inequality.
- `RationalChart.eventually_comap_mem_locus_iff`: under `h`, eventually, for
  every point `x` of `B`, `x` pulls back into `d.locus` along `φ t` if and only
  if it does along `ψ`. The positive lower bound is the Library's
  `exists_pos_le_denominator`.
- `RationalChart.spectralConvergesOn_of_factor`: assume `ψ` has image in
  `d.locus`, `ψd ∘ d.baseMap = ψ`, and eventually `φd t ∘ d.baseMap = φ t`.
  Then `ψd` and `φd` converge spectrally on every section of `d.algebra`. By
  `spectralConvergesOn_of_coordinates` it suffices to check the coordinates.
  Old coordinates are images of base coordinates. For a fraction coordinate,
  `map_fractionCoordinate_eq_inverse_mul` gives the value `u⁻¹ w`, with
  `u = φ t b` and `w = φ t f_j`, and `u₀⁻¹ w₀` for `ψ`. At a point `x` of `B`,
  `x u₀ ≥ ε₀`, and `x u = x u₀` once the denominator displacement is below
  `ε₀`. The identity
  `u⁻¹ w - u₀⁻¹ w₀ = u⁻¹ u₀⁻¹ (u₀ (w - w₀) - (u - u₀) w₀)` then bounds the
  displacement by `x u₀⁻² · max(‖b‖ δ, δ ‖f_j‖)`.

## Full represented domains

These results use Gerritzen–Grauert in the Library's form
`Domain.finiteRationalCover`: every `D : Domain K A` is covered by finitely
many rational charts with restrictions from `D`.

- `Domain.eventually_comap_mem_locus_iff`: under `h`, eventually, for every
  point `x` of `B`, `x` pulls back into `D.locus` along `φ t` if and only if it
  does along `ψ`. The locus is the union of the finitely many rational loci,
  and the rational case applies to each.
- `Domain.eventually_hasImageIn`: if `ψ` has image in `D.locus`, then
  eventually `φ t` does too.
- `Domain.spectralConvergesOn_of_factor`: if `ψ` has image in `D.locus`,
  `ψD ∘ D.baseMap = ψ`, and eventually `φD t ∘ D.baseMap = φ t`, then `φD` and
  `ψD` converge spectrally on every section of `D.algebra`. For each rational
  piece `d i`, pull back along `ψ` (Library `RationalChart.pullback`,
  `pullback_locus`, `pullbackMap`) to a rational chart `e i` of `B`. The limit
  map composed with the structural map of `e i` lands in `d i`. By the
  rational case it eventually does for `φ t` too. The universal property of
  `D` identifies the composites with the factorizations through `d i`. Every
  point of `B` lies in some `e i` and comes from its spectrum. The rational
  convergence on the finitely many pieces then gives the bound.

## Provenance and scope

This module is internal. It is a prerequisite for Berkovich continuity on
compact analytic pullbacks (Task 7765). It combines the Library's coordinate
approximation (`spectralConvergesOn_of_coordinates`), rational chart pullback,
fraction coordinates and Gerritzen–Grauert covering. No norm continuity,
common operator bound, nonempty spectrum or nontrivial valuation is assumed.
Only spectral (pointwise seminorm) bounds are concluded, not quotient-norm
bounds.
