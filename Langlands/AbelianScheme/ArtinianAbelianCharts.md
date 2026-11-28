# Constant charts of an abelian scheme as a chart family

Module `Langlands.AbelianScheme.ArtinianAbelianCharts` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`).

- `modelB` presents the constant abelian scheme `C` over `Spec R'` as a `Model` (module
  `ArtinianChartFamily`), with base change `CS` and special fibre `A₀` embedded by `τ`.
- `Charts.chartFamily` is the family of charts of `B` (module `ArtinianConstantCharts`) as a
  `ChartFamily` of this model, with residue map `jB`. For `R` local Artinian,
  `chartFamily_θS` identifies its transition maps with those of the original charts.
- `target` is the target `Target.ofGroup` of the group scheme underlying `C` (module
  `GroupTargetDifference`), used to measure lifts into `C`.

For `Charts.nonempty_liftedTransitions`, assume `R'` Artinian, `R` local Artinian and
`maximalIdeal R' * ker φ = 0`. Choose difference coordinates `b` for `C` and `ker φ`, a reduction
`F` of `C` modulo `maximalIdeal R'`, and lifts `D` of the transition maps that are inclusions on
the diagonal. Suppose that in each coordinate `j` the obstruction cocycle of `D`, observed
through the identity of `C`, is the Čech coboundary of a `1`-cochain `y j` on the residue
opens. Then the charts have lifted transition maps in the sense of `ArtinianLiftAssembly`.
The proof corrects `D` using `exactFamily` from `TransitionCoboundary`. The corrected maps
satisfy the cocycle condition and agree with `D` modulo `ker φ`, so they still reduce to `θS`.

## Provenance

SGA 1, Exposé III, §6, formula (4) and Théorème 6.3 give the correction by `g` when the
obstruction cocycle is `dg` (recomposed edition, arXiv math/0206203v2, printed pp. 65–66,
PDF pp. 81–82).
