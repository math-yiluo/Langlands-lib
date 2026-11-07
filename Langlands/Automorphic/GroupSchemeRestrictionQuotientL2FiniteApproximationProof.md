# Finite-level approximation in `L²([G])`: proof

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.quotientL2FiniteApproximation` proves
the published `QuotientL2FiniteApproximationStatement` of
`GroupSchemeRestrictionQuotientL2FiniteApproximationStatement`. The route
repeats the published positive-torus proof
`groupSchemeQuotientL2FiniteApproximation` for the published `[G]` action and
average. Notation is that of the statement Markdown: `ρf` is the finite right
action `rationalQuotientL2FiniteRightAction` on `L²([G])`, and `μ` is
`quotientHaarMeasure F G S j`.

## Norm bound for one average

`norm_rationalQuotientL2FiniteAverage_sub_le` takes an open subgroup `K` of
the finite adelic points with `[CompactSpace K]`, a vector `φ` and a real `ε`.
If `‖ρf k φ - φ‖ ≤ ε` for every `k : K`, then the average
`rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K φ` lies within `ε`
of `φ`. The published `rationalQuotientL2FiniteAverage_apply` writes the
average as the Bochner integral of the orbit against the published normalized
Haar probability measure `compactProbabilityHaar K`. Since that measure has
total mass one, the published integrability lemma and Mathlib's
`integral_sub` and `integral_const` turn the difference into the integral of
`ρf k φ - φ`. Mathlib's `norm_integral_le_of_norm_le_const` bounds it by `ε`.
The module uses the published local instances on `K` (topological group,
second countability, Borel σ-algebra) from the finite-average module.

## The sequence of subgroups

The published `finiteAdelicGroupCompactOpenBasis` proves that the compact open
subgroups of `FiniteAdelicGroupPoints F G` form a basis of the neighborhood
filter of `1`. The finite adelic points carry a published second-countable
topology, so this filter is countably generated. Mathlib's
`Filter.HasBasis.exists_antitone_subbasis` then gives a sequence `K n` of
open subgroups, proofs `hK n` that each is compact, and the antitone basis
property required by the statement.

## Fixed vectors and convergence

For each `n`, the published `rationalQuotientL2FiniteAverage_mem_fixedVectors`
puts the average over `K n` in `Langlands.fixedVectors ρf (K n).toSubgroup`.

For convergence, fix `φ` and `ε > 0`. The map `a ↦ ρf a φ` on the finite adelic
points is continuous: it is the published continuous orbit
`rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ` of
`GroupSchemeRestrictionQuotientL2Continuity`, composed with the published
continuous inclusion `AdelicGroupPoints.ofFinite F G`. At `a = 1` it takes the
value `φ`, so the set of `a` with `‖ρf a φ - φ‖ < ε / 2` is a neighborhood of
`1`. The antitone basis gives `N` with `K N` inside this set, and hence
`K n` inside it for every `n ≥ N`. For such `n`, the norm bound above gives
distance at most `ε / 2 < ε` between the average over `K n` and `φ`. This is
Mathlib's `Metric.tendsto_atTop`.

## Density

Each average over `K n` is fixed by the open subgroup `K n`, so it is a
`Langlands.IsSmoothVector` of `ρf`. The averages converge to `φ`, so `φ` lies
in the closure of the smooth vectors by Mathlib's `mem_closure_of_tendsto`.

## Scope

The proof uses only published results and Mathlib. It proves density for the
finite adelic action only. It does not prove archimedean smoothness or the
published `QuotientL2SmoothDensityStatement`.
