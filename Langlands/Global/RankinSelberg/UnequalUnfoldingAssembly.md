# Assembly of the unequal-rank unfolding: only the gauge premises remain

Module `Langlands.Global.RankinSelberg.UnequalUnfoldingAssembly`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Statement

- `UnequalUnfoldingGaugeSufficiencyStatement.{u}` is the implication
  `UnequalUnfoldingGaugeStatement.{u} → UnequalUnfoldingStatement.{u}`.
  - The hypothesis `UnequalUnfoldingGaugeStatement` (module `UnequalUnfoldingGaugeStatement`)
    states the gauge premises G and G' for every pair. These are the Library predicates
    `WhittakerGaugeIntegrable F h T T'` and `DualWhittakerGaugeIntegrable F h T T'`, for every
    number field `F : Type u` with `CompactSpace (AdeleQuotient F)`, all `t < r`, and actual
    cuspidal realizations `T` of rank `r + 1` and `T'` of rank `t + 1`. Each premise is an
    integrability bound with a threshold `C ≥ 0` that is uniform over standard characters and
    vectors.
  - The conclusion `UnequalUnfoldingStatement` (module `UnequalUnfoldingStatement`) is the
    ordinary and dual unfolding of Cogdell 2004, §2.2, for every actual positive unequal-rank
    cuspidal pair.

  The statement only links two published propositions. It adds no new mathematical content.

## Proofs

- `unequalUnfolding_of_premises (hCWE) (hDual) (hJ) (hG) : UnequalUnfoldingStatement` takes four
  inputs: the Whittaker expansion of cusp forms (`CuspidalWhittakerExpansionStatement`), the
  Whittaker expansion of dual cusp forms with locally uniform convergence
  (`DualCuspidalWhittakerExpansionStatement`), the modulus of right multiplication on adelic
  rectangles (`RectangleMeasureModulusStatement`) and the gauge premises. It applies the
  published conditional reduction `unequalUnfoldingReduction` to the four premises E, E', G and
  G' of each pair:
  - E is `projectionExpansionReduction F r t h T (hCWE F r T)` (module
    `ProjectionExpansionReduction`);
  - E' is `dualProjectionExpansionReduction hJ F r t h T (hDual F r T)` (module
    `DualProjectionExpansionReduction`);
  - G and G' are the two components of `hG` at the pair.
- `unequalUnfoldingGaugeSufficiency : UnequalUnfoldingGaugeSufficiencyStatement` supplies the
  first three inputs from published proofs:
  - `cuspidalWhittakerExpansionStatement_proof` (module `CuspidalWhittakerExpansionProof`);
  - `dualCuspidalWhittakerExpansionStatement_proof` (module `DualWhittakerExpansionProof`);
  - `rectangleMeasureModulus` (module `RectangleModulusProof`).
- `unequalUnfolding_of_whittakerGauges (hPad) (hRect)` combines this with the published
  conditional `unequalGaugeReduction` (module `UnequalGaugeReduction`). It derives
  `UnequalUnfoldingStatement` from the two open Whittaker majorant statements
  `UnequalPadGaugeStatement` and `UnequalRectGaugeStatement`.

## Accompanying renames

To import the new proof modules alongside the `DualExpansion*` modules, two lemmas of the
published modules `DualExpansionUnipotent` and `DualExpansionBridge` are renamed. Each clashed
with a different lemma of the same full name in another module:

- `Unfolding.haar_unipotentFundamentalDomain_lt_top` (in `DualExpansionUnipotent`) is now
  `Unfolding.unipotentFundamentalDomain_haar_lt_top`. The clash was with
  `WhittakerExpansionCore.WhittakerBasic`.
- `Unfolding.iota_mem_rationalSubgroup` (in `DualExpansionBridge`) is now
  `Unfolding.iota_mem_rationalSubgroup_of_mem`. The clash was with
  `DualWhittakerCore.DualDecay`.

The statements and proofs of the renamed lemmas are unchanged. Neither name is used outside its
own module.

Provenance: derived. The implication assembles published results. Cogdell 2004 (source
`cogdell-2004-analytic-theory-gln`, §2.2, printed pp.205–207) derives the unfolding from the
Whittaker expansion and the gauge estimates. The Library proves the expansion inputs, so the
gauge estimates are the only remaining hypothesis.
