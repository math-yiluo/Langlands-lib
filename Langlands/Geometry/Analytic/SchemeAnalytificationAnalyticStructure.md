# The analytic structure of the glued analytification of a scheme

This unit proves that the Library's `SchemeAnalytificationAnalyticStructureStatement`
follows from the Library's `SchemeAnalytificationGluingStatement`. The main
results are:

* `analyticStructure_of_openGluing (hg : OpenGluing K f)`: the conclusion of
  `SchemeAnalytificationAnalyticStructureStatement` for fixed `K`, `X`, `f`,
  assuming only the two gluing clauses in `OpenGluing K f` (every `ι K f U` is an
  open embedding, and the intersection formula for images of affine opens);
* `schemeAnalytificationAnalyticStructure_of_gluing`:
  `SchemeAnalytificationGluingStatement.{u} →
  SchemeAnalytificationAnalyticStructureStatement.{u}`, obtained by projecting
  clauses (2) and (3) of the gluing statement.

The gluing statement is published as a statement and is not yet proved. The
present unit therefore reduces the analytic-structure statement to it and proves
no unconditional instance.

## Construction

Fix `hg : OpenGluing K f`.

* `schemePresentation hg`: the saturated presentation with space
  `TopCat.of (Space K f)` and atlas `schemeAtlas hg`
  (`SchemeAnalytificationAtlas`), which has all local domains.
* `affineDomain hg U`: the analytic domain `range (ι K f U)`. It is open, and
  open subsets are analytic domains for atlases with all local domains
  (`HasAllLocalDomains.isOriginalChartDomain_of_isOpen`).
* `satChart K f U i`: the local chart `⟨U, saturatedRepresentative i⟩` given by a
  chart `i` of the saturated atlas of `U^an`. `satChart_image` computes its image.
  `satIndex hg U i` is the corresponding chart of `schemeAtlas hg`, and
  `satDomainIndex hg U i` is that chart viewed in `affineDomain hg U`.
* `toDomainStrong hg U` / `toDomain hg U`: the strong map from
  `saturated K (chartPresentation K f U)` to the domain presentation of
  `affineDomain hg U`. Its underlying map `toDomainBase hg U` is
  `y ↦ ⟨ι K f U y, _⟩`. Its pullback at an admissible pair `(i, j)` is the cross
  map `cross (satChart K f U i) (chartRep K f j.val)`. The admissible pairs are
  described by `image_subset_of_admissible` and `admissible_of_image_subset`.
  Chart compatibility is `cross_chart`. Restriction compatibility holds because
  both sides are compatible maps between the same local charts
  (`compatible_inclusion`, `cross_compatible`, `Compatible.comp`), and compatible
  maps are unique.
* `toDomain_isQuasiIso`: the underlying map is a homeomorphism (an embedding onto
  its range, by the open embedding `ι K f U`). Every pullback represents its chart
  image locus: that locus is `(chartRep K f j.val).chart ⁻¹' (satChart K f U i).image`,
  which the cross map represents by `represents_cross`.
* `affineIso hg U`: the isomorphism `localizedQuasiIso (toDomain hg U) _` in the
  localized category, from `AffineAnalytification.localized K (chartPresentation K f U)`
  to `localizationFunctor.obj ((schemePresentation hg).domain (affineDomain hg U))`.

## Proof of the three assertions

The witnesses are `S = schemePresentation hg`, `e = Homeomorph.refl`,
`D = affineDomain hg` and `φ = affineIso hg`.

1. `e '' (D U).carrier = range (ι K f U)` holds by definition (`Set.image_id`).
2. `(φ U).hom ≫ S.localizedDomainInclusion (D U)` is the image under
   `localizationFunctor` of `toDomain hg U ≫ S.domainInclusion (D U)`. By
   `localizedSpaceFunctor_map` its underlying map is that of the strong map, which
   is `ι K f U` (`toDomain_comp_inclusion_baseMap`).
3. Both sides are images under `localizationFunctor` of composites of strong
   maps, so it suffices to prove `saturatedHom_comp_toDomain`:
   `saturatedHom (restriction f h) ≫ toDomain hg U ≫ S.domainInclusion (D U) =
   toDomain hg V ≫ S.domainInclusion (D V)`.
   This uses the Library's `ext_of_saturated` (the source has all local domains).
   The underlying maps agree by the published `ι_localMap`. For each source chart
   `i` of `V^an`, choose a target chart `j₁` of the saturated hom and let
   `k = satIndex hg U j₁`. The pullbacks of both composites at `(i, k)` are
   computed by `comp_pullback` (the Library's `saturatedComp_pullback`). Each
   factor is compatible: `compatible_saturatedHom` for the saturated hom,
   `toDomain_pullback` for `toDomain`, and `domainInclusion_pullback` for the
   inclusion, whose pullbacks are atlas restrictions, that is, cross maps. Both
   composites are therefore compatible maps from `chartRep K f k` to
   `satChart K f V i`, and `compatible_unique` identifies them.

## Provenance

Internal proof unit. It implements the truth sketch in the Markdown of the
target statement `SchemeAnalytificationAnalyticStructureStatement`, which follows
Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), proof of Theorem 3.4.1, step (3), printed p.64/PDF p.78 (registered
source `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`). It also
follows Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Proposition 1.3.3, printed p.24/PDF p.21 (registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`). One point
departs from the sketch: the bounded restriction maps between charts coming from
different affine opens are not glued by Tate acyclicity. They are obtained from
the scheme-morphism calculus of `SchemeAnalytificationAffinoidPoints` and
`SchemeAnalytificationLocalCharts`. The only unproved inputs are clauses (2)
and (3) of `SchemeAnalytificationGluingStatement`.
