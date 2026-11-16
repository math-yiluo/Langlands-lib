# Assembly of Step 2a of Murre's induction

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteAssembly`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. A supporting module of the proof
of Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I,
Step 2a). Murre glues the representing scheme of `F` from the representing scheme `X'` over the
punctured spectrum and the closed-fibre charts `Spec B_y`, by his Lemma 3. This module performs
that gluing, assuming the infinitesimal étaleness of the charts away from their closed points;
that remaining input is proved in `MurreCompleteEtale`.

## `unramifiedRepresentable_of_chartEtale`

Let `R` be a complete local noetherian ring and `F` satisfy `MurreConditions`. Let
`e' : (baseChange (puncturedSpectrum R).ι F).RepresentableBy (Over.mk q')` with `q'` locally of
finite type and formally unramified, and let the `e k` represent `F` over `Spec (R/m^(k+1))` by
`q k`, formally unramified and locally of finite type. Assume (`het`) that for every `y : Y 0`
the element `chartElem e hF3 y` is infinitesimally étale at every non-closed point of
`Spec B_y`. Then `UnramifiedRepresentable F`.

Proof. The charts are indexed by `Option (Y 0)`:

* `none`: the object `X' → U → Spec R` (`U` the punctured spectrum, `j` its inclusion) with the
  universal element `e'.homEquiv (𝟙 _)`. It is locally of finite type and formally unramified
  (composites), a monomorphism (`LocalToGlobal.isMonoElement_map` of
  `isMonoElement_of_representableBy`) and infinitesimally étale at every point
  (`LocalToGlobal.infinitesimallyEtaleAt_map` of `infinitesimallyEtaleAt_of_representableBy`).
* `some y`: the chart `chartU e y` with `chartElem e hF3 y`. It is locally of finite type and
  formally unramified (`MurreCompleteMono`), a monomorphism (`chartElem_isMonoElement`, using (F1b)
  and (F6)), infinitesimally étale at the closed point
  (`chart_infinitesimallyEtaleAt_closedPoint`) and, by `het`, at the other points.

Every field-valued point `η` of `F` over `f : Spec K → Spec R` factors through a chart: if the
point of `Spec K` maps to the closed point, `K` kills `m` and `chart_cover` applies; otherwise
`f` factors through `U` (`IsOpenImmersion.lift`) and `η` is the image of
`e'.homEquiv.symm η` under `Over.map j`.

Murre's Lemma 3 (`ChartGluing.murreChartGluing`, using (F1a), (F1b), (F2), (F3) and `u`-small
values) now gives a scheme `Z` locally of finite type over `Spec R` representing `F`, with the
charts mapping to an open cover. `Z` is separated over `Spec R` by
`isSeparated_of_representableBy` (`MurreCompleteSeparated`, from (F6)). It is formally
unramified because formal unramifiedness is local on the source
(`IsZariskiLocalAtSource.of_openCover` for the open cover by the charts) and each chart is
formally unramified over `Spec R`.
