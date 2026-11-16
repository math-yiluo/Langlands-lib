# Premise E' from `J` and the dual Whittaker expansion

Module `Langlands.Global.RankinSelberg.DualProjectionExpansionReduction`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Statement

`DualProjectionExpansionReductionStatement.{u}`: assuming `RectangleMeasureModulusStatement.{u}`
(right multiplication `x ↦ x g` on `M_(k×m)(𝔸)` scales `rectangleMeasure F k m` by
`|det g|_𝔸^(-k)`), for every number field `F : Type u` with `CompactSpace (AdeleQuotient F)`, all
`t < r` and every actual cuspidal realization `T : CuspidalOperatorRealization F r`,
`DualCuspidalWhittakerExpansion F T → DualProjectionWhittakerExpansion F h T`.

`DualCuspidalWhittakerExpansion F T` (Library module `DualWhittakerExpansionStatement`): for
every standard `ψ` and vector `v`, the dual cusp form `φ̃ = dualFunction φ` is the absolutely
convergent sum of `W̃(diag(γ, 1) g)` over `N_r(F) \ GL_r(F)`, with `W̃ = dualFunction W`, and
the partial sums of the absolute values converge uniformly on compact sets.
`DualProjectionWhittakerExpansion F h T` is premise E' of the published
`UnequalUnfoldingReductionStatement` (Library module `UnfoldingDual`).

## Proof

`dualProjectionExpansionReduction` is
`dualProjectionWhittakerExpansion_of_dualCuspidalWhittakerExpansion` of module
`DualExpansionFinal`, whose Markdown describes the proof. The helper modules are
`DualExpansionPoints`, `DualExpansionSums`, `DualExpansionTorus`, `DualExpansionData`,
`DualExpansionCosets`, `DualExpansionLattice`, `DualExpansionUnipotent`, `DualExpansionRectangle`,
`DualExpansionStep`, `DualExpansionInduction`, `DualExpansionPeriodStep`,
`DualExpansionRectStep`, `DualExpansionRadical`, `DualExpansionConj`, `DualExpansionBridge`,
`DualExpansionRectMeasure`, `DualExpansionUnfold` and `DualExpansionFinal`.

## Role

With `RectangleMeasureModulusStatement` and `DualCuspidalWhittakerExpansionStatement` (both
published closed statements), this reduction discharges premise E' of
`UnequalUnfoldingReductionStatement` for every pair.

Provenance: derived. Cogdell 2004 (source `cogdell-2004-analytic-theory-gln`), §2.2, printed p.207 (PDF p.210) obtains the dual unfolding from the Whittaker expansion of the dual
cusp form. This candidate isolates that expansion and the modulus of right multiplication on
rectangles as hypotheses and proves the rest by an internal route.
