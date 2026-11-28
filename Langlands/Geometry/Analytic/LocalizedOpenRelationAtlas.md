# Charts of the glued space and their bounded maps

For gluing data `R : LocalizedOpenRelation K`, this module sets up the charts of
the glued space `Space R` (module `LocalizedOpenRelationSpace`) and the bounded
algebra maps between them. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation`.

## Charts of the pieces and morphisms from affinoid spectra

- `atl m` is the atlas of the saturated presentation `presentationOf (Z m)`.
- `PieceChart` is a pair of a piece `m` and a chart `i` of `atl m`; it has an
  algebra `alg`, a chart map `chart`, a domain `dom` (its range) and an image
  `image = ι m (dom)` in the glued space.
- `spec S` is the small spectrum `SmallAffinoidSpectrum.saturated S` of a presented
  affinoid algebra `S`, as an object of the localized category; `gchart S` is its
  global chart and `smap θ` the morphism of spectra of a bounded map `θ`.
- `cmap S c φ : spec S ⟶ Z c.m` is the localized chart map
  `SmallAffinoidSpectrum.chartMap S c.i φ` of a bounded map `φ : c.alg → S`, and
  `incl c = cmap c.alg c id`. Its points lie in `c.dom` (`cmap_mem`), it sends
  the point of a character `x` of `S` to `chart (comap φ x)` (`cmap_apply`), it is
  injective in `φ` (`cmap_injective`, from `localizedChartMap_injective`), every
  localized morphism from `spec S` with points in `c.dom` is of this form
  (`exists_cmap_eq`, from `localizedAffinoidChartFactorization`), and
  `smap θ ≫ cmap S c φ = cmap S' c (θ.comp φ)` (`smap_cmap`, from
  `map_comp_chartMap`).

## Factorization through a chart of a piece

`existsUnique_pbc`: let `f : spec S ⟶ Z m` have points whose images in the glued
space lie in `c.image` for a chart `c` of a piece. Then a unique bounded map
`φ : c.alg → S` has `Rel f (cmap S c φ)`. Proof: the points of `f` lie in
`domainSet m c.m`, so `f` has a transfer to `Z c.m`; its points lie in `c.dom` by
injectivity of `ι c.m`, so it is `cmap S c φ` for a unique `φ`, and every related
morphism is the transfer. `pbc` is this `φ` (`rel_pbc`, `pbc_unique`).

For charts `c d` of pieces with `c.image ⊆ d.image`, `rho c d h : d.alg → c.alg`
is `pbc` applied to `incl c`. It satisfies:

- `rel_rho`, `rho_unique`: `rho c d h` is the unique map with
  `Rel (incl c) (cmap c.alg d (rho c d h))`;
- `cmap_rho`: `Rel (cmap S c ψ) (cmap S d (ψ.comp (rho c d h)))`, by precomposing
  with `smap ψ`;
- `rho_self` and `rho_comp`: identity and composition laws;
- `rho_chart`: `ι d.m (d.chart (comap (rho c d h) x)) = ι c.m (c.chart x)`;
- `rho_universal`: let `φ : d.alg → S` be a bounded map whose induced spectrum map
  `BanachSpectrum.comap φ` lands in the inverse image of `c.image` under the chart of
  `d` followed by `ι d.m`, i.e. `ι d.m (d.chart (comap φ x)) ∈ c.image` for every point
  `x` of the spectrum of `S`. Then there is a unique `ψ : c.alg → S` with
  `ψ.comp (rho c d h) = φ`, namely `pbc` of `cmap S d φ`.

## Chart images and analytic domains

- `ChartImage` is the type of subsets of the glued space of the form `c.image`;
  `ChartImage.rep` chooses a chart `c` with that image (`rep_image`), and
  `chartMap T` is the chart map of `T.rep` followed by `ι` (`range_chartMap`).
- `isOriginalChartDomain_preimage_image`: the trace on any piece `Z m` of the image
  of a chart of a piece is an analytic domain of `atl m`. It is the image in
  `Z m` of the preimage of the chart under the transfer of the inclusion of the
  open domain `domainSet m c.m` (`domainPreimage`), extended through the open domain
  (`OriginalChartDomain.subspaceExtend`).

## Provenance

Internal. These are the chart-level counterparts of the gluing isomorphisms of
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993), §1.3,
printed p.24 / PDF p.21 (`berkovich-1993-etale-cohomology`), read off from the
Library's affinoid chart factorization of localized morphisms.
