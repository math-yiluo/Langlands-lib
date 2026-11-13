# Renard II.3.13 Corollary: center of the category and invariant distributions

Worker 108 and Worker 42, Task 5531. Source: David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered `renard-2026-representations-groupes-reductifs-padiques`,
II.3.13 Corollary and its proof (printed pp.55–56 / PDF pp.61–62), and
I.1.7 (printed pp.12–13 / PDF pp.18–19) for the categorical comparison.

`statements : Statements.{uG, uM}` proves the published
`Langlands.HarmonicAnalysis.Distribution.RenardCenter.Statements` at both
universe parameters: `uG` for the group, and `uM`, with the categorical center
taken over nondegenerate modules in universe `max uG uM`. The statement is the conjunction
`CriteriaStatement.{uG} ∧ CategoricalCenterStatement.{uG, uM}`. The proof
adds no hypotheses. It combines published results with two helper modules
submitted together with this file.

## Route

`statements_of` derives `Statements.{uG, uM}` from the two published
propositions `RenardEssentialProducts.Statements.{uG}` (II.3.13 Lemma) and
`RenardCompletion.Statements.{uG}` (II.3.13 Theorem). It builds the pair as
follows.

* First conjunct: the published theorem `criteria : CriteriaStatement.{uG}`
  from `RenardCenterCriteriaProof`. It covers the translation, trace and
  compact-open sandwich criteria for conjugation invariance of an arbitrary
  algebraic distribution. Renard does not print these full-dual criteria as
  separate results. They are an internal extraction of the local-test argument
  in his proof of II.3.13, and their provenance and proof are explained in
  `RenardCenterCriteriaProof.md`.
* Second conjunct: `categoricalCenterStatement_of` from the helper module
  `RenardCenterCategoricalProof`. It needs the two propositions above and,
  for every group, Haar measure and right product `pr` satisfying
  `RightProductSpecification`, the centrality specification
  `CentralitySpecification μ pr`. That last input is `centrality` from the
  helper module `RenardCenterCentralityProof`.

`statements` applies `statements_of` to the published proofs
`RenardEssentialProducts.statements` and `RenardCompletion.statements`.

## The helper modules

* `RenardCenterCentralityProof` (Worker 108): every right product satisfying
  the published right specification satisfies `CentralitySpecification`. Its
  center equals the Hecke commutant. Commuting with both full Hecke actions is
  conjugation invariance, by the translation criterion. Invariant right
  essentially compact distributions are two-sided essentially compact.
* `RenardCenterCategoricalProof` (Worker 42): Renard I.1.7. The published map
  `NondegenerateModuleCenter.fromCommutantRingHom` from the commutant of the
  canonical image in `IdempotentedRingRightLimit` to the categorical center is
  bijective. Then, for the completion comparison `E`, `E⁻¹` sends the
  commutant bijectively onto the conjugation-invariant essentially compact
  distributions. Composing gives the equivalence `C` with every clause of
  `CategoricalComparisonSpecification`: additivity, products via the
  two-sided product `p`, unit `dirac 1`, and the identification with `E` and
  the commutant map.

Each helper module has its own paired Markdown with the details.
