# Descent along finite étale affinoid covers, chart by chart on the base

Throughout, `K` is a complete ultrametric normed field, possibly trivially
normed. `f : A → B` is a finite Banach map of presented affinoid algebras with
`v`-small spectra. `M(A)` and `M(B)` are the objects
`localizationFunctor.obj (SmallAffinoidSpectrum.saturated A)` and so on of the
localized category `LocalizedCategory.{u, v, v}`, and
`M(f) = localizationFunctor.map (SmallAffinoidSpectrum.map f)`. A localized map
`g : M(B) ⟶ T` *equalizes `M(f)`* if `a ≫ g = b ≫ g` for all `a`, `b` with
`a ≫ M(f) = b ≫ M(f)`. For a saturated atlas presentation `S` and a chart `i`,
`ιᵢ` denotes the localized small chart inclusion
`localizationFunctor.map (S.smallChartSpectrumInclusion i)`.

The main theorem constructs the descent `h` with `M(f) ≫ h = g` when
the charts of `M(A)` over whose preimage `g` lands in a single chart of
`T` locally refine `M(A)`.

## Auxiliary results

- `AffinoidPushout.rightMap_flat_of_tensorComparison` shows that if the comparison from
  the ordinary tensor product `C ⊗_A B` to the completed pushout is bijective
  and `f` is flat, then the right pushout map `C → AffinoidPushout.algebra f g`
  is flat. The comparison is an isomorphism of `C`-algebras, and flatness
  is base-changed.
- `AffinoidPushout.comap_rightMap_surjective` shows that surjectivity on Banach spectra
  passes from `f` to the right pushout map. A point of `M(C)` and a point of
  `M(B)` with the same image in `M(A)` come from a point of the pushout
  (`AffinoidPushout.exists_point`).
- By `localizedChartIso_hom_comp`, the localized small chart inclusion `ιᵢ` is the
  isomorphism `smallChartDomainIso` followed by the localized inclusion of the
  chart domain. Hence every localized map whose points land in the range of
  chart `i` factors through `ιᵢ` (`exists_smallChartLift`), and the
  monomorphism property gives `smallChartInclusion_cancel`.
- `localizedSpaceFunctor_map_comp_apply` computes the point map of a composite.
- `surjective_localizedSpaceFunctor_map_map` passes surjectivity on Banach
  spectra to the point map of `M(f)`.

## `map_eq_of_baseMap_eq`

If `f` is finite Banach and `g` equalizes `M(f)`, then `g` is constant on the
fibres of `M(f)`. For two points `y`, `y'` of `M(B)` with the same image in
`M(A)`, the small spectrum of the self-pushout of `f` has a point `t` over
`(y, y')` by `SmallAffinoidSpectrum.pushout_exists_point`. The two
projections agree after composing with `M(f)` and therefore also after
composing with `g`. Evaluating at `t` gives equality of the images of
`y` and `y'`.

## `exists_baseChange_descent`

Let `f` be finite Banach, flat and surjective on spectra, let `ρ : A → C` be a
bounded map, and let `g : M(B) ⟶ T` equalize `M(f)`. Let
`j : M(Q) ⟶ T` be a monomorphism from a small affinoid spectrum. Let
`U` be a set of points of `T` such that every localized map with points in `U`
factors through `j`. Suppose that `g` maps every point of `M(B)` lying over the
image of `M(ρ)` into `U`. Then there is `l : M(C) ⟶ T` with `w ≫ l = p ≫ g`
whenever `w ≫ M(ρ) = p ≫ M(f)`.

Proof. Let `P` be the small spectrum of the completed pushout of `f` and `ρ`.
By `pushout_localized_isPullback`, `M(P)` is a pullback of `M(f)` and `M(ρ)` in
the localized category. The right map `r : C → P` is finite Banach
(`finiteBanachPushout`), flat (first auxiliary result together with
`finiteTensorComparison`) and surjective on spectra. The composite
`M(P) ⟶ M(B) ⟶ T` has its points in `U`, so it factors as `m ≫ j`. Because `j`
is a monomorphism and `g` equalizes `M(f)`, `m` agrees on the two projections
of the self-pushout of `r`. `SmallAffinoidSpectrum.exists_unique_localizedHomDescent`
(module `FiniteProjectiveBoundedDescent`) descends `m` to `M(C)`. Composing
with `j` gives `l`. The required equation follows from the pullback property.

## `exists_chart_descent`

This is the previous result for a chart `c` of `M(A)` and a chart `e` of a
saturated atlas presentation `T`. If `g` maps every point of `M(B)` lying over
the range of `c` into the range of `e`, then there is a localized map `l` from
the small spectrum of `c` to `T` with `w ≫ l = p ≫ g` whenever
`w ≫ ι_c = p ≫ M(f)`. The localized inclusion `ι_c` is `M(ρ)` for a bounded
map `ρ` (`localizedMapEquiv`), and `j = ι_e`, `U = range e` satisfy the
hypotheses by the auxiliary results.

## `descent_compat_of_etale`

Let `π : Y ⟶ X` be étale and surjective on points, and let `g : Y ⟶ T`.
Suppose `l₁ : V₁ ⟶ T` and `l₂ : V₂ ⟶ T` satisfy `w ≫ lₖ = p ≫ g` whenever
`w ≫ iₖ = p ≫ π`. Then `a ≫ l₁ = b ≫ l₂` whenever `a ≫ i₁ = b ≫ i₂`.
The étale base change `localizedEtalePullbackBaseChange` of `π` along
`a ≫ i₁` gives a pullback `P` with an étale map `q : P ⟶ W`. That map is
surjective on points by `exists_point_of_isPullback_of_etale`. Both
composites `q ≫ a ≫ l₁` and `q ≫ b ≫ l₂` equal `p ≫ g`, and
`etaleCoverHomExt` cancels `q`.

## `GoodBaseChart` and `exists_hom_of_finiteEtale_of_locallyRefines`

`GoodBaseChart f T g c` says that there is a chart `e` of `T` such that `g`
maps every point of `M(B)` lying over the range of the chart `c` of `M(A)`
into the range of `e`.

**Theorem.** Let `f : A → B` be finite Banach, algebraically finite étale
(`BoundedAlgHom.AlgebraicallyFiniteEtale`) and surjective on Banach spectra.
Let `T` be a saturated atlas presentation and let
`g : M(B) ⟶ localizationFunctor.obj T` equalize `M(f)`. Suppose that the
ranges of the charts `c` with `GoodBaseChart f T g c` locally refine
`{univ}` in the space of `M(A)`. Then there is
`h : M(A) ⟶ localizationFunctor.obj T` with `M(f) ≫ h = g`.

Proof. `M(f)` is étale (`map_etale_of_finite_pointwiseEtale`) and surjective
on points. `exists_chart_descent` gives a local descent `l c` on every
good chart `c`. The family is compatible by `descent_compat_of_etale`, and
`exists_hom_of_chartCover` glues it to `h` with `ι_c ≫ h = l c`. For the
equation `M(f) ≫ h = g`, `locallyRefines_charts_into` shows that the charts
of `M(B)` mapped by `M(f)` into a good chart cover `M(B)`. On such a chart `d`
the map `ι_d ≫ M(f)` factors through `ι_c` (`exists_smallChartLift`). The
defining property of `l c` then gives `ι_d ≫ M(f) ≫ h = ι_d ≫ g`, and
`localizedHom_ext_of_chartCover` concludes.

The gluing follows the existence part of the proof of Berkovich’s
Proposition 4.1.3 on printed pages 83–84. It descends on affinoid
domains of the base whose preimages map into an affinoid domain of the
target. Remark 4.1.5 relates the covering hypothesis to the image
property for affinoid domains under finite étale maps.
[Berkovich, *Étale cohomology for non-Archimedean analytic spaces*](https://www.numdam.org/item/PMIHES_1993__78__5_0/)
