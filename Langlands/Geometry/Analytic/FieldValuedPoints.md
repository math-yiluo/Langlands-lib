# Field-valued points of analytic spaces

Author: Worker 21.

This module defines the points of an analytic space with values in a normed
field `L` over the ground field `K`. It shows that they form a functor on the
localized category of analytic spaces (the category on which the étale site
`Ét(X)` of module `EtaleSite` is built). All declarations lie in
`Langlands.Analytic`.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, §1.4,
printed p.30 / PDF p.27: "We remark that with each point x ∈ X ∈ Φ-𝒜n one can
associate a non-Archimedean field ℋ(x) over k so that, for any Φ-affinoid
domain V ⊂ X that contains x, there is a canonical bounded character
𝒜_V → ℋ(x) that identifies ℋ(x) with the corresponding field of the point x
with respect to V (see [Ber], 1.2.2 (i)). A morphism φ : Y → X induces, for
each point y ∈ Y, an isometric embedding ℋ(φ(y)) → ℋ(y)."

An `L`-valued point below is a point together with such a compatible family of
characters with values in `L`, one for each chart containing the point. In the
source, the canonical characters into `ℋ(x)` give such a family with
`L = ℋ(x)`; this is not formalized here. The definition
by compatible families over all charts is derived. It avoids identifying the
completed residue fields of different charts, which is a theorem not used
here. The functoriality and the inversion of quasi-isomorphisms below are
derived constructions.

## `L`-valued points

Fix a normed field `L` with `[NormedAlgebra K L]`.

- `IndexedAffinoidAtlas.exists_mem_range_chart`: every point lies in a chart,
  because the chart ranges form a quasinet.
- `AffinoidAtlasPresentation.FieldPoint L A`: a structure with
  - `point : A.space`;
  - `eval i h : A.atlas.algebra i →ₐ[K] L` for every chart `i` whose range
    contains the point;
  - `isChartPoint`: for every such chart there is a spectrum point `p` with
    `chart i p = point` and `‖eval i h a‖ = p a` for all `a`;
  - `eval_restriction`: `eval i ∘ restriction i j = eval j` whenever the range
    of chart `i` lies in that of chart `j`.
- `FieldPoint.ext'`: two `L`-valued points agree when their points and all
  their evaluations agree.
- `FieldPoint.eval_comp_eq`: evaluation at a chart, composed with a map into
  its algebra, can be computed at any smaller chart containing the point.

## Functoriality along strong maps

Let `f : StrongHom A B` be a strong map whose source atlas contains all local
domains (`hA : A.atlas.HasAllLocalDomains`).

- `StrongHom.exists_admissible_mem`: if `f x` lies in the target chart `j`, then
  `x` lies in a source chart `i` with `f(V_i) ⊆ V_j`. Take any chart `i₀`
  containing `x` and a target chart `k ⊇ f(V_{i₀})`. The net property gives a
  target chart `m ⊆ V_j ∩ V_k` containing `f x` (Library
  `exists_chart_inter`). The Library's `exists_chart_inter_preimage` gives a
  source chart with range `V_{i₀} ∩ f⁻¹(V_m)`.
- `FieldPoint.eval_comp_pullback_eq`: for two such source charts `i`, `i'`,
  `eval i ∘ f.pullback i j = eval i' ∘ f.pullback i' j`. Both equal the value
  at a chart `m ⊆ V_i ∩ V_{i'}` containing the point, by the restriction
  equation `restriction_comm` of strong maps.
- `FieldPoint.pushEval`, `pushEval_eq`, `map`, `map_point`, `map_eval`: the
  image point `f.map` has point `f x` and evaluation
  `eval i ∘ f.pullback i j` at the target chart `j`, for any admissible `i`.
  - Its seminorm condition uses the spectrum point `comap (f.pullback i j) p`
    and the Library's `chart_comm`.
  - Its restriction equation is `restriction_comm` with equal source charts.
- `FieldPoint.map_id`, `FieldPoint.map_saturatedComp`: the identity and the
  saturated composition (Library `saturatedComp_pullback`) are respected.
- `SaturatedAtlasPresentation.fieldPointFunctor L`:
  `SaturatedAtlasPresentation.{u, v, w} K ⥤ Type (max u v w uL)`, with
  `fieldPointFunctor_obj` and `fieldPointFunctor_map_apply`.

## Inversion of quasi-isomorphisms

Let `s : StrongHom A B` be a quasi-isomorphism (`hs : s.IsQuasiIso`) and let `B`
contain all local domains (`hB`). In namespace `StrongHom.IsQuasiIso`:

- `exists_chart_eq_image`, `imageChart`, `range_imageChart`,
  `imageChart_admissible`: the image `s(V_i)` of a source chart is the range of
  a target chart `imageChart i`. It is the chart of the local domain
  `hs.localDomain i k` (Library `HasAllLocalDomains.exists_chart`).
- `represents_univ`: the pullback `s.pullback i (imageChart i)` represents the
  whole spectrum, since the chart image locus is everything.
- `chartInverse`: its inverse, the Library's `Represents.univInverse`;
  `chartInverse_comp`, `comp_chartInverse` are the two inverse laws, and
  `chartInverse_pullback` computes `chartInverse ∘ s.pullback i j` as the
  target restriction from `imageChart i` to `j`.

In namespace `FieldPoint`:

- `eval_congr`: evaluations of equal points agree.
- `comapQuasiIso hs hB q`: the `L`-valued point of `A` over an `L`-valued point
  `q` of `B`. Its point is the preimage of `q.point` under the homeomorphism
  `s`. Its evaluation at chart `i` is `q.eval (imageChart i) ∘ chartInverse i`.
  - Its spectrum point is `comap (chartInverse i) r` for the spectrum point `r`
    of `q`; injectivity of `s` identifies its chart image.
  - Its restriction equation follows from `restriction_comm` and the inverse
    laws.
- `map_comapQuasiIso`: `s.map (comapQuasiIso q) = q`, by
  `chartInverse_pullback` and the restriction equation of `q`.
- `map_injective`: `s.map` is injective. Points agree by injectivity of `s`.
  Evaluations at chart `i` agree because they are the evaluations of the
  images at `imageChart i`, composed with `chartInverse i`
  (`comp_chartInverse`).
- `map_bijective`.

## The localized category

- `fieldPointFunctor_inverts`: `fieldPointFunctor L` sends the
  quasi-isomorphisms of saturated presentations to bijections, hence to
  isomorphisms (Mathlib's `isIso_iff_bijective`).
- `localizedFieldPointFunctor L`:
  `LocalizedCategory.{u, v, w} ⥤ Type (max u v w uL)`, the descent through the
  Library's `descend`. `localizationFunctor_localizedFieldPointFunctor` is
  the descent equation.
- `fieldPointProjection L`: the natural map to the underlying points,
  `p ↦ ULift.up p.point`, into `spaceFunctor ⋙ forget TopCat ⋙ uliftFunctor`.
- `localizedFieldPointProjection L`: its descent to the localized category,
  into `localizedSpaceFunctor ⋙ forget TopCat ⋙ uliftFunctor`, by Mathlib's
  `Localization.Construction.natTransExtension`.
  `localizedFieldPointProjection_app` gives its value on the image of a
  saturated presentation.

## Scope

Not proved here:

- that the completed residue field of a point does not depend on the chart,
  and hence that an `L`-valued point is determined by one chart;
- existence of `L`-valued points over a given point;
- the universal property of `L`-valued points as morphisms from `M(L)`.
