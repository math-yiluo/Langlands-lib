# Finite-sum form and continuity of the Whittaker pairing

This supporting module is a helper for the proof of
`Langlands.Whittaker.WhittakerCompletenessStatement` (Jacquet and Shalika 1985,
Lemma 3.2). That proof deforms test representations through a parameter. It
needs the pairing `∫ H f` with a fixed test function `H` to be continuous in the
parameter. This module proves the continuity. It holds because the integral is a
finite sum of values of `H f`. The module states and proves no result from the
literature.

## The general finite-sum formula

Let `G` be a topological group, `N` a subgroup and `N \ G` the published left
coset space `QuotientIntegration.LeftQuotient N`, with its quotient topology.

- `orbit N K g` is the image in `N \ G` of the coset `g K`, i.e. the set of
  classes of `g k` for `k ∈ K`. This is the module's only definition.
- `mk_mem_orbit`: the class of `g` lies in `orbit N K g`.
- `orbit_eq_of_mk_mem`: if the class of `x` lies in `orbit N K g`, then
  `orbit N K x = orbit N K g`.
- `disjoint_orbit`: two different orbits are disjoint.
- `descend_eq_of_mem_orbit`: a function `F` on `G` that is left `N`-invariant and
  right `K`-invariant descends to `N \ G`, and the descended function is constant
  with value `F g` on `orbit N K g`.
- `isOpen_orbit`: if `K` is open, every orbit is open. It is the image of the open
  set `g K` under the open quotient map.
- `exists_integral_descend_eq_sum`: let `μ` be a measure on `N \ G` that is finite
  on compact sets, with open sets measurable. Let `K` be an open subgroup and `C` a
  compact subset of `G`. Then there are a finite set `s ⊆ G` and real weights
  `m c` with the following property. Every `F : G → ℂ` that is left
  `N`-invariant, right `K`-invariant and vanishes outside `N C` satisfies
  `∫ descend F dμ = ∑ c ∈ s, m c • F c`. The set and the weights depend only on
  `N`, `K`, `C` and `μ`, not on `F`.

The proof of `exists_integral_descend_eq_sum` runs as follows. The image of `C`
in `N \ G` is compact. The open orbits `orbit N K c`, `c ∈ C`, cover it, so
finitely many do. Among the finitely many points `c` chosen,
`Finset.exists_subset_injOn_image_eq_of_surjOn` keeps one point `s` per distinct
orbit, so the orbits of the points of `s` are pairwise disjoint. Pointwise,
`descend F` equals `∑ c ∈ s, F c · 1_(orbit N K c)`. On a covered orbit this holds
by `descend_eq_of_mem_orbit` and disjointness. Off all covered orbits both sides
vanish, because `F` vanishes outside `N C`. The integral is then
`∑ c ∈ s, μ(orbit N K c) • F c`, so `m c = μ.real (orbit N K c)`. Each term is
integrable: if `F c ≠ 0`, the orbit lies in the image of `C`, which has finite
measure.

## The Whittaker specialization

Over a nonarchimedean local field `F` with `G = GL_(n+1)(F)` and `N` the upper
unipotent subgroup:

- `exists_integral_whittakerProductIntegrand_eq_sum`: let `H` be a compact
  Whittaker test function for `ψ` (`IsCompactWhittakerTestFunction`), `μ` a
  measure on `N \ G` finite on compact sets, and `K` an open subgroup. Then there
  are a finite set `s` and weights `m` with
  `∫ whittakerProductIntegrand ψ H f dμ = ∑ c ∈ s, m c • (H c · f c)` for every
  right `K`-invariant inverse-character function `f`. The proof applies the
  general formula to `F = H f`, with the open subgroup `K ⊓ K_H` (`K_H` is the
  invariance group of `H`) and the compact support set of `H`.
- `tendsto_integral_whittakerProductIntegrand`: let `f i` be inverse-character
  functions, all right invariant under one open subgroup `K`, converging pointwise
  along a filter to a right `K`-invariant function `f₀`. Then
  `∫ whittakerProductIntegrand ψ H (f i) dμ` tends to
  `∫ whittakerProductIntegrand ψ H f₀ dμ`. Both sides are the same finite sum, so
  this is a finite sum of limits.
- `integral_whittakerProductIntegrand_eq_zero_of_tendsto`: under the same
  hypotheses, along a nontrivial filter, if the pairings with `f i` eventually
  vanish, then the pairing with `f₀` vanishes. This is uniqueness of limits.

The pointwise convergence and the common invariance group are hypotheses here.
For the deformed Whittaker functions of a family of twisted representations they
are proved separately.

## Provenance

The module is internal. It packages, for the published quotient integral
(`QuotientIntegration.descend`) and the published pairing integrand
(`RankinSelberg.whittakerProductIntegrand`), the standard fact that integrals of
compactly supported, locally constant functions on a totally disconnected space
are finite sums. It was written for the proof of `WhittakerCompletenessStatement`.
No statement here is attributed to a source.
