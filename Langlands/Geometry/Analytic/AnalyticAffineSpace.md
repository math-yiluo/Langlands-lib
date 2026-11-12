# The analytic affine space as an increasing union of closed polydiscs

Author: Worker 21.

This module constructs the `d`-dimensional analytic affine space over a
nontrivially valued complete ultrametric field `K`. It is glued from the
increasing chain of closed polydiscs `E(0, ‖ϖ‖⁻ᵐ)`, `m ∈ ℕ`, along the radius
restrictions. The module proves that the glued space is Hausdorff and equips it
with an indexed affinoid atlas, a directed rational atlas, and the two
corresponding atlas presentations. It is the ambient space of Drinfeld's upper
half space.

All declarations lie in `Langlands.Analytic.AnalyticAffineSpace`.

## Original source and derived provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
PDF SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

- Definition 1.5.1, printed p.19 / PDF p.33: the affine space `𝔸ⁿ` is the set
  of multiplicative seminorms on `k[T_1, …, T_n]` bounded on `k`, with the
  weakest topology making all `x ↦ |f(x)|` continuous. Remark 1.5.2(i), same
  page: "`𝔸ⁿ = ⋃ E(0, r)`", with `E(0, r) = 𝓜(k{r⁻¹T})`.
- §3.4 ("GAGA: the case of nontrivial valuation"), proof of Theorem 3.4.1,
  step (1), printed p.64 / PDF p.78: "One has `𝔸ⁿ = ⋃_{r>0} E(0, r) =
  ⋃_{r>0} D(0, r)` (equality of sets), where `D(0, r)` is the open subset
  `{x ∈ E(0, r) | |T_i(x)| < r_i, 1 ≤ i ≤ n}` of the `k`-affinoid space
  `E(0, r) = 𝓜(k{r⁻¹T})`. … In particular, `𝔸ⁿ` is a `k`-analytic space
  (obviously closed)."

The atlas conventions are those of the existing `IndexedAffinoidAtlas`, after
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, Definition 1.2.3, printed p.16
/ PDF p.13.

Derived choices. The source's union runs over all positive polyradii; here
only the cofinal chain of constant polyradii `‖ϖ‖⁻ᵐ` is used, for one fixed
`ϖ ∈ K` with `0 < ‖ϖ‖ < 1`. The space is built by gluing these closed
polydiscs along the radius restrictions of `PolydiscRestriction`, not as the
set of multiplicative seminorms on `K[T]`. The identification of the glued
space with Berkovich's seminorm space, and its independence of `ϖ`, are not
proved here. Nontriviality of the valuation provides `ϖ` and matches the
setting of Berkovich's §3.4.

## Radii

`scale K` is an element `ϖ` with `0 < ‖ϖ‖ < 1`, chosen once from
`NormedField.exists_norm_lt_one` (`norm_scale_pos`, `norm_scale_lt_one`).
`radius K m = ‖ϖ‖⁻¹ ^ m`. It is positive and strictly increasing in `m`
(`radius_pos`, `radius_strictMono`, `radius_le_radius_iff`,
`radius_lt_radius_succ`), and at least `1` (`one_le_radius`). `polyradius K d m` is the constant polyradius on
`Fin d` with value `radius K m`, and `disc K d m` is the closed polydisc
`polydisc K d (polyradius K d m)`, that is, `K{(‖ϖ‖⁻ᵐ)⁻¹T}`.

From here `K` is ultrametric and complete.

## The chart system and the glued space

`restriction K d h` for `h : m ≤ k` is the radius restriction
`Polydisc.restriction` (module `PolydiscRestriction`) from `disc K d k` to
`disc K d m`.
`represents_restriction` restates `Polydisc.represents_restriction` with the
represented set written as the spectrum image, as required by
`AffinoidChartSystem`.

`chartSystem K d` is the `AffinoidChartSystem` with index type `ℕ`, chart
algebras `disc K d m`, inclusions `m ≤ k`, and restrictions as above.
Functoriality is `Polydisc.restriction_self` and `Polydisc.restriction_trans`.
The meet condition holds because one of two indices below `k` is below the
other.

`Space K d` is the glued space `(chartSystem K d).Space` (a quotient of the
disjoint union of the polydisc spectra), and `chart K d m` is the chart of the
`m`-th polydisc.

- `pull_coordinate` and `coordinate_glued`: restriction preserves the values
  `|T_i(x)|`, so glued points have equal coordinate norms.
- `coordinateNorm K d i` is the continuous function `z ↦ |T_i(z)|` on the glued
  space (`coordinateNorm_chart`, `continuous_coordinateNorm`).
- `mem_range_chart_iff`: a point lies in the `m`-th polydisc iff
  `|T_i(z)| ≤ ‖ϖ‖⁻ᵐ` for all `i`. One direction is the bound of a spectrum point
  by the norm and `‖T_i‖ ≤ ‖ϖ‖⁻ᵐ`. For the other, a point of a larger polydisc
  with these bounds is in the spectrum image of the restriction, by
  `Polydisc.range_comap_restriction`.
- `openDisc K d m = {z | |T_i(z)| < ‖ϖ‖⁻⁽ᵐ⁺¹⁾ for all i}` is open
  (`isOpen_openDisc`). It contains the `m`-th and is contained in the
  `(m+1)`-st closed polydisc. Hence the `(m+1)`-st polydisc is a neighborhood
  of every point of the `m`-th (`range_chart_mem_nhds`).
- `hasFiniteOverlaps`: two glued points of the `i`-th and `j`-th polydiscs come
  from the single common subdomain `min i j`. So every chart is a closed
  embedding (`isClosedEmbedding_chart`, from the published gluing lemma).
- The `T2Space` instance: two points lie in a common open disc, which is
  contained in a closed polydisc chart, a Hausdorff subspace. The published
  `t2Space_of_separated_or_open_t2` concludes.

## The atlases

This part assumes `NeZero d`.

- `basePointHom K d m` is bounded evaluation of `disc K d m` at the `K`-rational
  point `(ϖ⁻ᵐ, 0, …, 0)`; its weighted monomial bound is `‖ϖ⁻ᵐ‖ = ‖ϖ‖⁻ᵐ`.
  `basePoint K d m` is the pulled-back field norm. `coordinateNorm_basePoint`
  computes `|T_0| = ‖ϖ‖⁻ᵐ` there.
- `range_chart_subset_iff`: the `m`-th polydisc lies in the `k`-th iff
  `m ≤ k`. The base point shows the forward direction, because the radii are
  strictly increasing.
- `atlas K d : IndexedAffinoidAtlas.{u, u, 0} K (Space K d)` has charts the
  closed polydiscs. Distinct indices give distinct chart images. The chart
  family is a net: each point of the `m`-th polydisc has the `(m+1)`-st as a
  neighborhood, and the intersection of two polydiscs is the smaller one,
  which is itself a member. The restriction for an inclusion of chart images
  is the radius restriction, and its universal property is
  `represents_restriction`.
- `atlas_hasDirectedCharts`: any two polydiscs lie in the polydisc of the larger
  index.
- `presentation K d : AffinoidAtlasPresentation.{u, u, 0} K` is the space with
  this atlas.
- `rationalAtlas K d : IndexedAffinoidAtlas.{u, u, u} K (Space K d)` is the
  published `DirectedRationalAtlas.atlas` of the polydisc atlas: its charts are
  all rational domains of all the closed polydiscs.
  `rationalPresentation K d : AffinoidAtlasPresentation.{u, u, u} K` is the
  corresponding presentation, with index universe equal to the space universe.

## Scope

No structure sheaf, maximal atlas or comparison with the analytification of
`Spec K[T_1, …, T_d]` is constructed. The case `d = 0` is excluded from the
atlases (all polydiscs are then one point, so chart images would coincide).
