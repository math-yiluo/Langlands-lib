# Local chart covers and gluing equality along a source refinement

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It is internal.

## Local chart covers

`IsLocallyChartCovered T Q Z y` says the following. There are finitely many
charts of `T` with property `Q`, all containing `y` and contained in `Z`, whose
union contains `Z ∩ N` for some neighbourhood `N` of `y`. Results:

- `isLocallyChartCovered_of_isQuasinet`: sets whose restricted chart family is
  a quasinet.
- `isLocallyChartCovered_chart`: charts.
- `isLocallyChartCovered_of_mem_nhds`: neighbourhoods. This uses the Library's
  `HasAllLocalDomains.exists_finite_chart_nhds_subset`.
- `isLocallyChartCovered_analyticDomain`: analytic domains.
- `isLocallyChartCovered_of_cover`: finite covers by such sets.
- `IsLocallyChartCovered.inter`: intersections. Pairs of charts are refined by
  the net property.
- `isLocallyChartCovered_chart_inter_preimage` and
  `isLocallyChartCovered_preimage`: preimages of a target chart under a strong
  map. Target charts in an intersection are pulled back by
  `StrongHom.exists_chart_inter_preimage`.
- `IsLocallyChartCovered.of_subset_pred`: attaching a property that all
  subcharts of `Z` have.

## Gluing

`localizationFunctor_map_eq_of_local_eq` takes strong maps
`x₀ x₁ x₂ : S ⟶ A`, a set `L` of points of `A` that is Hausdorff as a subspace,
and a finite set `C` of charts contained in `L` and covering `L`. Assume:

- the image of `x₀` lies in `L`;
- the three maps have the same preimages of the charts of `C`;
- on every chart of `S` that `x₀` maps into a chart `c ∈ C`, the pullbacks of
  `x₁` and `x₂` to `c` agree.

Then `localizationFunctor.map x₁ = localizationFunctor.map x₂`.

Proof. The charts of `S` mapped by `x₀` into charts of `C` form a
downward-closed selection. It is locally refining. Near a point `y` of a chart
`P₀`, the charts of `C` not containing `x₀ y` are compact in the Hausdorff `L`,
hence closed there. So points near `y` are sent into charts of `C` through
`x₀ y`, and `P₀ ∩ x₀⁻¹(c)` is locally chart covered for each such `c`. The
refining inclusion `r` is a quasi-isomorphism
(`isQuasiIso_refiningSubatlasInclusion`). The two base maps agree, because
pullbacks determine images of points (`chart_comm`). By `ext_of_saturated` and
`refiningSubatlasInclusion_comp_pullback`, `r ≫ x₁ = r ≫ x₂`, and the
localization of `r` is invertible.
