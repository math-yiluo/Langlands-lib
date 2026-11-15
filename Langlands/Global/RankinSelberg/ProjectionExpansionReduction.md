# Premise E from the Whittaker expansion of cusp forms

Module `Langlands.Global.RankinSelberg.ProjectionExpansionReduction`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Statements

- `CuspidalWhittakerExpansionStatement.{u}`: for every number field `F : Type u` with
  `CompactSpace (AdeleQuotient F)`, every `r : ℕ` and every actual cuspidal realization
  `T : CuspidalOperatorRealization F r`, `CuspidalWhittakerExpansion F T` holds. That is, for
  every standard additive character `ψ`, vector `v` and `g ∈ GL_(r+1)(𝔸)`, the family
  `q ↦ W(cornerAdelicPoint F r q.out · g)` over `N_r(F) \ GL_r(F)` is absolutely summable with
  sum `φ(g)`, where `W = cuspWhittaker F T ψ v` and `φ = cuspFunction F T v`. This is the
  pointwise part of the Whittaker expansion of cusp forms: Cogdell 2004 (source
  `cogdell-2004-analytic-theory-gln`), Theorem 1.1, printed p.200 (PDF p.203); Library
  `Langlands.Global.WhittakerExpansionStatement` with all `m_i = 1`, specialized to the vectors
  of actual cuspidal realizations. It is stated, not proved.
- `ProjectionExpansionReductionStatement.{u}`: for every such `F`, all `t < r` and every
  `T : CuspidalOperatorRealization F r`,
  `CuspidalWhittakerExpansion F T → ProjectionWhittakerExpansion F h T`. The conclusion is
  premise E of the published `UnequalUnfoldingReductionStatement` (module `UnfoldingOrdinary`):
  for every standard `ψ`, `v` and `g ∈ GL_m(𝔸)` (`m = t + 1`), the sum over
  `N_m(F) \ GL_m(F)` of `|det g|^{-(n-m-1)/2} W(diag(γ g, I_(n-m)))` converges unconditionally
  to `projection F _ ψ φ (diag(g, 1))`.

## Proof

`projectionExpansionReduction : ProjectionExpansionReductionStatement` is
`projectionWhittakerExpansion_of_cuspidalWhittakerExpansion` of module `ProjectionExpansion`,
whose Markdown explains the column induction. It uses the helper modules `ProjectionPeriod`,
`ProjectionColumns` and `ProjectionRadical`.

## Role

With `CuspidalWhittakerExpansionStatement`, this reduction discharges premise E of
`UnequalUnfoldingReductionStatement` for every pair. `CuspidalWhittakerExpansionStatement` is
expected to follow from the Library's `WhittakerExpansionStatement` once its hypotheses are
verified for realization vectors: finite plot smoothness, uniform moderate growth (Library
`AdelicAutomorphicUniformGrowthStatement`) and standard block cuspidality.

Provenance: derived. The implication isolates the analytic input of Cogdell's derivation of the
projection expansion (p.205), the Whittaker expansion of the cusp form, and proves the rest.
