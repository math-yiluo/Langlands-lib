# Finite-level approximation on `L²([G])` and its a.e. cuspidal subspace: proof

Authors: Worker 112 (proof drafts) and Worker 1788 (self-contained assembly).

`Langlands.Global.RestrictionSplitCentre.quotientFullAEL2FiniteApproximation`
proves the published `QuotientFullAEL2FiniteApproximationStatement` of
`GroupSchemeRestrictionFullAEL2FiniteApproximationStatement`. Its type is
exactly that proposition. Notation is that of the statement Markdown: `μ` is
`quotientHaarMeasure F G S j`, `ρf` is the finite right action
`rationalQuotientL2FiniteRightAction` on `L²([G]) = Lp ℂ 2 μ`, `Sq` is the
a.e. cuspidal subspace, `A n` and `B n` are the averages over `K n` on
`L²([G])` and on `Sq`, and `P`, `Q` are the orthogonal and ambient
projections.

The module does not depend on an unpublished proof. It proves the ambient
conclusions itself, in two `private` helpers. Their route is Worker 112's
draft proof of the published `QuotientL2FiniteApproximationStatement`, which
repeats the published positive-torus proof
`groupSchemeQuotientL2FiniteApproximation`. The helpers are private, so their
names do not clash with a later public proof of that ambient statement. Only
the closing theorem is exported.

## Norm bound for one average

The private helper `norm_finiteAverage_sub_le` takes an open subgroup `K` of
the finite adelic points with `[CompactSpace K]`, a vector `φ` and a real `ε`.
If `‖ρf k φ - φ‖ ≤ ε` for every `k : K`, then the average
`rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K φ` lies within `ε`
of `φ`. The published `rationalQuotientL2FiniteAverage_apply` writes the
average as the Bochner integral of the orbit against the published normalized
Haar probability measure `compactProbabilityHaar K`. That measure has total
mass one. So the published `rationalQuotientL2FiniteAverage_integrable` and
Mathlib's `integral_sub` and `integral_const` turn the difference into the
integral of `ρf k φ - φ`. Mathlib's `norm_integral_le_of_norm_le_const` bounds
this integral by `ε`. The section uses the published local instances on `K`
(topological group, second countability, Borel σ-algebra) from the
finite-average module.

## Ambient approximation

The private helper `ambientFiniteApproximation` has as its type the published
`QuotientL2FiniteApproximationStatement`, imported by its Lean name.

- The sequence of subgroups. The published `finiteAdelicGroupCompactOpenBasis`
  proves that the compact open subgroups of `FiniteAdelicGroupPoints F G`
  form a basis of the neighborhood filter of `1`. The finite adelic points
  carry a published second-countable topology, so this filter is countably
  generated. Mathlib's `Filter.HasBasis.exists_antitone_subbasis` then gives
  a sequence `K n` of open subgroups, proofs `hK n` that each is compact, and
  the antitone basis property.
- Fixed vectors. For each `n`, the published
  `rationalQuotientL2FiniteAverage_mem_fixedVectors` puts the average over
  `K n` in `Langlands.fixedVectors ρf (K n).toSubgroup`. Here
  `CompactSpace (K n)` comes from `hK n` by Mathlib's
  `isCompact_iff_compactSpace`, as in the statement.
- Convergence. Fix `φ` and `ε > 0`. The map `a ↦ ρf a φ` on the finite adelic
  points is continuous. It is the published continuous orbit
  `rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ` composed with the
  published continuous inclusion `AdelicGroupPoints.ofFinite F G`. At
  `a = 1` it takes the value `φ`, so the set of `a` with
  `‖ρf a φ - φ‖ < ε / 2` is a neighborhood of `1`. The antitone basis gives
  `N` with `K N` inside this set, and then `K n` lies inside it for every
  `n ≥ N`. For such `n`, the norm bound puts the average over `K n` within
  `ε / 2 < ε` of `φ`. Mathlib's `Metric.tendsto_atTop` concludes.
- Density. Each average over `K n` is fixed by the open subgroup `K n`, so it
  is a `Langlands.IsSmoothVector` of `ρf`. The averages converge to `φ`, so
  `φ` lies in the closure of the smooth vectors by Mathlib's
  `mem_closure_of_tendsto`.

## The closing theorem

`quotientFullAEL2FiniteApproximation` applies `ambientFiniteApproximation` to
the same data, forgetting `hG` and `hPD`. This gives `K`, `hK`, the antitone
basis and the three conclusions about `A n` on `L²([G])`. The remaining
conclusions come from the published module
`GroupSchemeRestrictionFullAEL2FiniteAverage`, with `CompactSpace (K n)`
obtained from `hK n` as above.

- `(B n ψ).val = A n ψ.val` is the published
  `quotientFullAEL2CuspidalFiniteAverage_val`.
- `B n ψ` lies in the fixed vectors of the cuspidal finite action for `K n`
  by the published `quotientFullAEL2CuspidalFiniteAverage_mem_fixedVectors`.
- Convergence of `B n ψ` to `ψ` in `Sq`: by Mathlib's `tendsto_subtype_rng`,
  it is equivalent to convergence of the underlying vectors `(B n ψ).val` in
  `L²([G])`. By the identity above these are `A n ψ.val`, which converge to
  `ψ.val` by the ambient conclusion.
- Density in `Sq`: each `B n ψ` is fixed by the open subgroup `K n`, so it is
  a finite smooth vector, and `ψ` lies in the closure of these vectors by
  `mem_closure_of_tendsto`.
- `P (A n φ) = B n (P φ)` is the published
  `quotientFullAEL2CuspidalOrthogonalProjection_finiteAverage`, and
  `Q (A n φ) = A n (Q φ)` is the published
  `quotientFullAEL2CuspidalAmbientProjection_finiteAverage`.

## Scope

The proof uses only published results and Mathlib. It proves density for the
finite adelic actions only. It proves no archimedean smoothness and no
existence of nonzero cusp forms.
