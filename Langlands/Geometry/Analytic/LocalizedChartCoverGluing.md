# Gluing localized maps on chart covers and refining maps into chart covers

This module proves two results about the localized analytic category
`LocalizedCategory` of saturated atlas presentations over a complete
ultrametric normed field `K`; the valuation of `K` may be trivial. A family
of charts *covers* a presentation `A` when the ranges of the charts form a
quasinet of the space of `A`: in Lean, `AtlasTopology.LocallyRefines` of
the family of chart ranges against `{univ}`. Each chart has its small
spectrum `A.smallChartSpectrum i` and the strong inclusion
`A.smallChartSpectrumInclusion i` into `A`; below, `ιᵢ` denotes the
localized inclusion `localizationFunctor.map (A.smallChartSpectrumInclusion i)`.

## `exists_hom_of_chartCover`

Let `A : SaturatedAtlasPresentation.{u, v, v} K`, let `i : ι → Index` be a
family of charts covering `A`, with `ι` in an arbitrary universe, and let `Y`
be an object of `LocalizedCategory.{u, v, v}`. Suppose that for every `k`
a localized map `l k` from the small spectrum of chart `i k` to `Y` is
given, and that the family satisfies the following compatibility: for all
`k`, `j`, every object `T` and all maps `a` and `b` from `T` to the small
spectra of the charts `i k` and `i j` with `a ≫ ι_{i k} = b ≫ ι_{i j}`, one
has `a ≫ l k = b ≫ l j`. Then there is a localized map
`L : localizationFunctor.obj A ⟶ Y` with `ι_{i k} ≫ L = l k` for every `k`.
Such an `L` is unique by `localizedHom_ext_of_chartCover` (module
`LocalizedChartCoverLifts`).

The proof follows `exists_lift_of_chartCover` (module
`LocalizedChartCoverLifts`). The isomorphism `smallChartDomainIso` identifies the small spectrum of a chart
with the original domain object of that chart, compatibly with the
inclusions into `A`. Transporting `l k` along it gives a quotient arrow on
each original chart domain. On the intersection of two chart domains, the
two nested domain inclusions, composed with the comparison isomorphisms,
form a pair `a`, `b` with equal composites into `A`; the compatibility
hypothesis therefore gives the overlap equation of a
`QuotientDomainMatchingFamily`. Its `glue` is the required map, and
`glue_restrict` together with the chart comparison gives
`ι_{i k} ≫ L = l k`.

## `exists_chartCover_refinement`

Let `A` and `B` be saturated atlas presentations in
`SaturatedAtlasPresentation.{u, u, u} K`, let `i : ι → Index` be a family of
charts covering `A`, and let `f : localizationFunctor.obj B ⟶
localizationFunctor.obj A` be a localized map. Then there are a
presentation `S`, a strong quasi-isomorphism `s : S ⟶ B` and a set `J` of
charts of `S` covering `S` such that for every `m ∈ J` there are an index
`k` and a localized map `g` from the small spectrum of chart `m` to the
small spectrum of chart `i k` with
`g ≫ ι_{i k} = ι_m ≫ localizationFunctor.map s ≫ f`.

The proof takes a common strong numerator `F : S ⟶ A` of `f` on a
quasi-isomorphic source, by `exists_commonStrongNumerators` (module
`LocalizedPullbackDescent`),
so that `localizationFunctor.map s ≫ f = localizationFunctor.map F`. Let
`J` be the set of charts of `S` whose range is carried by the base map of
`F` into the range of one chart of the family. To see that `J` covers `S`,
fix a point `y` of `S`. The quasinet property gives finitely many charts of
the family that contain `F y` and whose union is a neighbourhood of `F y`.
For each of them, `isLocallyChartCovered_preimage` (module
`QuasiEtaleRigidity.RefinementGluing`) gives
finitely many charts of `S` that contain `y`, lie in the preimage of that
chart, and cover the preimage near `y`. All these charts lie in `J`, and
their union contains the intersection of the preimage of the neighbourhood
with the finitely many neighbourhoods of `y`, which is a neighbourhood of
`y` because the base map of `F` is continuous. For `m ∈ J` mapped into
chart `i k`, with `h` the inclusion of ranges, the identity of strong maps
`S.smallChartSpectrumInclusion m ≫ F =
SmallAffinoidSpectrum.map (F.pullback m (i k) h) ≫ A.smallChartSpectrumInclusion (i k)`
follows from `SmallAffinoidSpectrum.chartMap_comp` and
`SmallAffinoidSpectrum.map_comp_chartMap`. Applying `localizationFunctor.map`
and using `localizationFunctor.map s ≫ f = localizationFunctor.map F` turns
it into the required equation with the localized inclusions `ι_m` and
`ι_{i k}`, where `g` is the localization of
`SmallAffinoidSpectrum.map (F.pullback m (i k) h)`.

## Provenance: internal

Both results are internal consequences of the Library's gluing of quotient
arrows on original chart domains (`QuotientDomainMatchingFamily.glue`), the
chart comparison `smallChartDomainIso`, strong numerators of localized maps
(`exists_commonStrongNumerators`) and the local chart covers of preimages
of charts under strong maps (`isLocallyChartCovered_preimage`). They are the
localized forms of two facts about the Grothendieck topology of analytic
domains of Berkovich spaces: morphisms glue along a quasinet of affinoid
domains, and a morphism into a space covered by a quasinet of affinoid
domains becomes, on a quasinet of affinoid domains of its source, a family
of morphisms into members of the cover. No original source is transcribed.
