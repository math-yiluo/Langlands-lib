# Compact-probe coverings on Hausdorff objects

`Langlands.Analytic.SaturatedAtlasPresentation.compactProbeQuasiEtaleHausdorffComparison K`
proves
[`CompactProbeQuasiEtaleHausdorffComparisonStatement.{u, v} K`](CompactProbeQuasiEtaleHausdorffComparisonStatement.md)
for every complete ultrametric normed field `K`. For `X : LocalizedCategory.{u, v, v} (K := K)`,
an object `U` of `QuasiEtaleSite X` whose underlying space is Hausdorff and a
sieve `S` on `U`, it shows that `S ∈ compactProbeQuasiEtaleTopology X U` if
and only if `HasQuasiEtaleChartNeighborhoods S.arrows`. The theorem has no
other hypothesis. The base `X` and the sources of the arrows of `S` may be
non-Hausdorff. The proof uses no fibre-product statement and no point-lifting
hypothesis: the compact pullbacks and the point lifting it needs are the
theorems `compactQuasiEtalePullbacks` and
`exists_point_of_isPullback_over_compactQuasiEtale`. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

Throughout, "compact Hausdorff object" means `IsCompactSpace`, which asks
for a compact and Hausdorff underlying space.

## Auxiliary facts

All helpers below are private to the module.

- `finite_subcover_of_chart_neighborhoods`: let `C` be compact and `T` a set
  of subsets. If each point of `C` has a neighbourhood that is the union of
  finitely many members of `T`, then finitely many members of `T` cover `C`.
  This is the finite subcover property of `C`.
- `exists_compact_domain_containing`: in an object with Hausdorff underlying
  space, every compact subset lies in an analytic domain `D` such that
  `domainObj A D` is compact Hausdorff. The atlas charts form a net
  (`isNet_chartFamily`), so `IsQuasinet.exists_finite_cover_of_isCompact`
  covers the compact set by finitely many chart ranges. Their union is an
  original chart domain (`isOriginalChartDomain_of_finite_chart_cover`) and
  is a compact domain (`isCompactDomain_of_eq_iUnion`).
- `domainSiteObject`, `domainSiteInclusion`, `domainSiteLift`: for an
  analytic domain `D` of a Hausdorff site object `U`, the composite
  `domainι U.left D ≫ U.hom` is quasi-étale by
  `hasLocalDomainEtaleFactorizations_of_quasiEtale`. This makes `D` a site
  object with an inclusion arrow into `U`. An arrow into `U` whose image lies
  in `D` factors through this inclusion (`domainLift`, and
  `domainSiteLift_comp`).

## Covering sieves have chart neighbourhoods

`has_chart_neighborhoods_of_compact_probes`. Fix a point `x` of `U`. The
space of `U` is weakly locally compact by
`IsQuasinet.weaklyLocallyCompactSpace`, because its chart net consists of
compact sets, so `x` has a compact neighbourhood `C`. Choose a compact domain
`D` containing `C` and apply the compact-probe test to the inclusion of `D`.
It gives finitely many arrows `f i : V i ⟶ D` with compact Hausdorff sources.
Each composite with the inclusion lies in `S`, and together they hit every
point of `D`. Each compact space `V i` is covered by finitely many chart
ranges of its atlas. The images of these chart domains under the composites
are finitely many sets of the form required by
`HasQuasiEtaleChartNeighborhoods`. Joint surjectivity onto `D` shows that
their union contains `C`, hence is a neighbourhood of `x`.

## Chart neighbourhoods give covering sieves

- `exists_compact_quasiEtale_charts`: a compact subset of the space of any
  site object `V` is covered by finitely many chart domains of `V` whose
  inclusions, composed with `V.hom`, are quasi-étale. At each point,
  `isLocalizedQuasiEtaleAt_of_quasiEtale` gives finitely many charts whose
  union is a neighbourhood. For each of them (`IsQuasiEtaleChart`), the
  inclusion of the chart domain followed by `V.hom` equals an affinoid
  domain embedding followed by an étale arrow, so it is quasi-étale by
  `quasiEtale_comp_of_isAffinoidDomainEmbedding_of_etale`.
  Compactness then leaves finitely many charts. `V` need not be Hausdorff
  here.
- `compact_images_cover_of_chart_neighborhoods`: if `S` satisfies the
  chart-neighbourhood condition, then every compact subset of `U` is covered
  by finitely many ranges of arrows `W ⟶ U` in `S` with compact Hausdorff
  source `W`. Each chart domain in a neighbourhood witness is compact
  (`isCompactDomain_chartDomain`), so the previous item covers it by
  finitely many quasi-étale chart domains of the source `V`. Each of these
  is a compact Hausdorff site object (`isCompactSpace_chartDomainObj`). Its
  inclusion followed by the arrow `V ⟶ U` lies in `S` by downward closure.
  The range of this composite is the image of the chart domain. A finite
  subcover is then taken as in `finite_subcover_of_chart_neighborhoods`.

`compact_probes_of_has_chart_neighborhoods`. Let `g : C ⟶ U` be an arrow
from a compact Hausdorff site object. The range of `g` is compact, so the
previous item gives finitely many arrows `f R : V R ⟶ U` in `S` with compact
Hausdorff sources whose ranges cover it. The union of the range of `g` and
the ranges of the `f R` is compact. Since `U` is Hausdorff, it lies in a
compact domain `D`, and `g` and every `f R` factor through `D`.
`compactQuasiEtalePullbacks`, applied over the compact object `D`, gives
pullback cones `T R` of the factored arrows with compact Hausdorff apexes.
Their underlying squares are pullbacks of analytic spaces. The first
projections `T R ⟶ C` form the required family. Each composite with `g`
equals the second projection followed by `f R`, which lies in `S`. For a
point `x` of `C`, choose `R` and a point `y` of `V R` with the same image
in `U`. Their images in `D` then agree. Since `D` is compact Hausdorff and
quasi-étale over `X`, `exists_point_of_isPullback_over_compactQuasiEtale`
lifts the pair to a point of `T R` over `x`. The finite index set is
reindexed by `Fin` with `Fintype.equivFin`.

`compactProbeQuasiEtaleHausdorffComparison` combines the two directions.

## Sources

The chart-neighbourhood condition is from Berkovich, *Vanishing cycles for
formal schemes*, Invent. Math. 115 (1994), §3, printed p. 544 (PDF p. 6),
literature ID `berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
The compact pullbacks and the point lifting used in the second direction
follow the analytic fibre-product geometry of Berkovich, *Étale cohomology
for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78 (1993),
Proposition 1.4.1, printed pp. 29–30 (PDF pp. 26–27), literature ID
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The equivalence itself is a derived comparison between the Library's
compact-probe topology and Berkovich's condition. Neither paper states it.
