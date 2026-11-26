# Morphisms of algebraic spaces induce morphisms of analytifications

The theorem `spaceAnalytificationMorphism` proves
`SpaceAnalytificationMorphismStatement.{u}` in every universe `u`. Let `K` be
a complete ultrametric nontrivially normed field, let `f : X' ⟶ X` be a
morphism of algebraic spaces over `Spec K` with `X'` separated and locally of
finite type, and let `(Y', p')` and `(Y, p)` be analytifications of `X'` and
`X` in the sense of `IsAnalytification`. Then there is exactly one morphism
`F : Y' ⟶ Y` in `LocalizedCategory.{u, u, u}` with
`p' A P x ≫ F = p A P (RingPoints.map f x)` for every test algebra `A`,
finite polynomial presentation `P` of `A` and point `x` of `X'` with values
in `A`. Nothing is assumed of `X` beyond the analytification `(Y, p)`.

The proof does not use the étale Hom-sheaf condition
`SpaceAnalytificationMorphismEtaleDescentInput` of the module
`SpaceAnalytificationMorphismReduction`. It builds `F` by gluing along a
cover of `Y'` by affinoid charts and proves uniqueness with the étale
detection theorem `etaleCoverHomExt`. Both hypotheses on `X'` are used:
separatedness in `IsAnalytification.comp_map_eq_of_comp_eq` and in the
affinoid point maps, and local finite type in the affinoid point maps and in
`exists_polynomial_point_factorization`.

## The chart cover of `Y'`

Write `Y'` as the localization of a saturated atlas presentation `A₀`. The
theorem `exists_affinoidPointHom_pair_chartCover` (module
`SpaceAnalytificationAffinoidChartCover`), applied to the identity of `Y'`
twice, gives a presentation `A`, an isomorphism
`e : localizationFunctor.obj A ≅ Y'` and a set `I` of charts of `A`
covering `A`, such that for each chart `k ∈ I` with algebra `R` the map
`ι_k ≫ e.hom` is the affinoid point map `affinoidPointHom` of some point of
`X'` with values in `R`; here `ι_k` is the localized small chart spectrum
inclusion. This cover theorem uses the étale test points of `X'`: through
`exists_affinoidPointHom_neighborhood` (module
`SpaceAnalytificationAffinoidChartNeighborhoods`) it places each point of a
chart in the image of the analytic map of an étale test point (axioms
`jointly_surjective` and `etale_map` of `IsAnalytification`) and takes a
surjective finite étale chart pair there. By
`exists_polynomial_point_factorization` (module
`SpaceAnalytificationAffinoidPoints`) the point of `X'` attached to chart `k`
is the image of a test point
`z k` of `X'`, with values in a finitely presented algebra with presentation
`Q k`, under an algebra map into `R`. By `affinoidPointHom_test` there is
a map `g k` with `g k ≫ p' (z k) = ι_k ≫ e.hom`.

## Existence

On chart `k` put `l k = g k ≫ p (f ∘ z k)`. If maps `a` and `b` into the
small spectra of charts `k` and `j` satisfy `a ≫ ι_k = b ≫ ι_j`, then
`(a ≫ g k) ≫ p' (z k) = (b ≫ g j) ≫ p' (z j)`, and
`IsAnalytification.comp_map_eq_of_comp_eq` (module
`SpaceAnalytificationMorphismCompatibility`) gives `a ≫ l k = b ≫ l j`.
This is the compatibility hypothesis of `exists_hom_of_chartCover` (module
`LocalizedChartCoverGluing`), which glues the `l k` to a map `L` with
`ι_k ≫ L = l k`. Put `F = e.inv ≫ L`.

The proof then shows: for every object `T`, every map `w : T ⟶ Y'` and
every test point `y` of `X'` with a map `c` satisfying `c ≫ p' y = w`, one
has `w ≫ F = c ≫ p (f ∘ y)`. Write `T` as the localization of a
presentation. The theorem `exists_chartCover_refinement` (module
`LocalizedChartCoverGluing`), applied to `w ≫ e.inv` and the cover `I`,
gives a quasi-isomorphism `s` onto `T` and a chart cover of its source
whose charts `m` map into charts `k ∈ I` through maps `g'` with
`g' ≫ ι_k = ι_m ≫ s ≫ w ≫ e.inv`. Since `s` becomes an isomorphism and
the charts `m` detect equality of localized maps
(`localizedHom_ext_of_chartCover`), it suffices to compare the two sides on
each chart `m`. There the left side is `g' ≫ l k = (g' ≫ g k) ≫ p (f ∘ z k)`,
and `(g' ≫ g k) ≫ p' (z k) = ι_m ≫ s ≫ w = (ι_m ≫ s ≫ c) ≫ p' y`, so
`IsAnalytification.comp_map_eq_of_comp_eq` identifies it with the right
side. Taking `w = p' A P x` and `c = 𝟙` gives the required compatibility of
`F` with every test point.

## Uniqueness

Let `G` be compatible with every test point. The analytic maps `p' x` of
the étale test points `x` of `X'` are étale by the axiom `etale_map` and
jointly surjective onto `Y'` by the axiom `jointly_surjective`. After
composition with each of them, `G` and `F` both give `p (f ∘ x)`. Hence
`G = F` by `etaleCoverHomExt` (module `EtaleCoverHomExt`).

## Sources

The statement follows Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`: Theorem 2.2.3 (printed
pp.7–8), and in §4.1 the paragraph on printed p.19 beginning "The arguments
in §2 carry over essentially verbatim", which gives functoriality of
analytification in the sense of `k`-analytic spaces. That paragraph is
followed in §4.1 by the base-extension paragraph and Theorem 4.1.4, whose
proof continues onto p.20. There functoriality is obtained from étale charts
and the étale topology of Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), §4.1, registered as `berkovich-1993-etale-cohomology`.
The Lean proof takes a different route. It obtains a cover of `Y'` by
affinoid charts from the jointly surjective étale test maps, glues the
chart maps by quotient-domain gluing on analytic domains, and applies
`etaleCoverHomExt` to the étale test maps for uniqueness; it does not use a
sheaf property of `Hom(-, Y)` for the étale topology.
