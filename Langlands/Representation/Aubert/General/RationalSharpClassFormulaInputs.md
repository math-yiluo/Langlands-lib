# Inputs for the signed class formula on the actual rational points

Module `Langlands.Representation.Aubert.General.RationalSharpClassFormulaInputs`.

The final theorem `rationalSharpClassFormulaReduction` proves the reduction
proposition of the statement module
[`RationalSharpReductionStatements`](RationalSharpReductionStatements.md). The
module has zero errors and zero warnings, and the final theorem uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The module uses:

* the generic reduction
  `Langlands.Aubert.General.SharpClassFormula.class_formula_of_exact`, from
  `SharpClassFormulaReduction`;
* the endpoint-free conditional exactness theorem
  `RationalPointFamily.rationalIsExactBeforeTerminal_of_inputs`, from
  `RationalCorrectedExactnessReduction`.

The module is conditional and does not prove the target. It proves the
published reduction proposition
`RationalPointFamily.RationalSharpClassFormulaReductionStatement`, which says:
the target `RationalPointFamily.RationalSharpClassFormulaStatement` follows
from four propositions that the Library states but does not prove. The
target is Aubert 1995, Corollaire 3.9 (a), on the actual rational-point
families, extended to finite-length members of `Alg({I})` as in the 1996
erratum, p. 4690.

All content is internal and derived. Apart from these inputs it formalizes no
new statement of the literature.

## Declarations

* `jacquet_subsingleton_of_card_lt` (generic families). Assume association
  preserves the number of labels. Then `SupportCategoryJacquetVanishingTarget`
  gives `Subsingleton (r_K E)` for every `E` in `Alg({I})` and every `K` with
  `K.card < I.card`. Proof: suppose `J ⊆ K` and `I` is associated to `J`. Then
  `I.card = J.card ≤ K.card`, which contradicts `K.card < I.card`.
* `RationalPointFamily.rationalSharpClassFormula_of_inputs` (conditional).
  - Inputs: `H : RationalCorrectedExactnessInputs.{u, v}` and
    `RationalSupportCategoryJacquetVanishingStatement.{u, v}`.
  - Conclusion: `RationalSharpClassFormulaStatement.{u, v}`.
  - Proof steps:
    1. Introduce the binders of the target.
    2. Get `StandardComplex.IsExactBeforeTerminal … E I` from
       `rationalIsExactBeforeTerminal_of_inputs H`.
    3. Get `Subsingleton (r_K E)` for `K.card < I.card` from
       `jacquet_subsingleton_of_card_lt`, with `rootAssociation_card_eq` as
       the label-count law.
    4. Apply `SharpClassFormula.class_formula_of_exact` at universes
       `u, u, max (u + 1) v`. That theorem applies the finite exact Euler
       identity to the degree objects and identifies the terminal homology
       with `E#`.
* `RationalPointFamily.rationalSharpClassFormula_of_remaining` (conditional).
  - Inputs: support Jacquet vanishing and four of the five fields of
    `RationalCorrectedExactnessInputs`:
    `RationalCorrectedGradedVanishingStatement`,
    `RationalCorrectedGradedTransitionStatement`,
    `RationalSupportCategoryInductionJacquetStatement` and
    `RationalSupportCategoryExactnessDetectionStatement`.
  - Conclusion: the target.
  - The Bruhat field is the published theorem
    `Langlands.GroupScheme.rationalBruhat`.
* `RationalPointFamily.rationalSharpClassFormula_of_open` (conditional).
  - Inputs: `RationalCorrectedGradedVanishingStatement`,
    `RationalSupportCategoryInductionJacquetStatement`,
    `RationalSupportCategoryExactnessDetectionStatement` and support Jacquet
    vanishing.
  - Conclusion: the target.
  - The graded-transition field is the published theorem
    `RationalPointFamily.rationalCorrectedGradedTransitionStatement`, from
    `RationalCorrectedGradedTransitionProof`.
* `RationalPointFamily.rationalSharpClassFormula_of_association`
  (conditional).
  - Inputs: the first three inputs of `rationalSharpClassFormula_of_open` and
    `RationalCuspidalSupportAssociationStatement.{u, v}`.
  - Conclusion: the target.
  - Support Jacquet vanishing comes from the published conditional theorem
    `rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`.
    Its compactness premise is discharged by the published
    `Langlands.BruhatTits.dynamicParabolicQuotientCompact`.
* `RationalPointFamily.rationalSharpClassFormulaReduction : RationalSharpClassFormulaReductionStatement.{u, v}`.
  This is the theorem that proves the published reduction proposition.
  - The proposition is the curried implication
    `RationalCorrectedGradedVanishingStatement → RationalSupportCategoryInductionJacquetStatement → RationalSupportCategoryExactnessDetectionStatement → RationalSupportCategoryJacquetVanishingStatement → RationalSharpClassFormulaStatement`,
    at universes `{u, v}`.
  - The proof takes the four hypotheses `hgv hind hdet hvan` and returns
    `rationalSharpClassFormula_of_open hgv hind hdet hvan`.
  - The binders and universes of the inputs and of the conclusion are those
    of the published propositions. The theorem adds no other premise.
  - The target's finite-length proof `hfl`, used to build `D_G`, stays
    universally quantified inside `RationalSharpClassFormulaStatement`.

## Remaining inputs

The Library proves none of the following. For four of them it has
only conditional reductions:
`rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`,
`rationalSupportCategoryExactnessDetection_of_zeroDetection`,
`rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
and `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`.

| Input |
| --- |
| `RationalCorrectedGradedVanishingStatement` |
| `RationalSupportCategoryInductionJacquetStatement` |
| `RationalSupportCategoryExactnessDetectionStatement` |
| `RationalSupportCategoryJacquetVanishingStatement` |
| or `RationalCuspidalSupportAssociationStatement` |

`RationalCorrectedGradedTransitionStatement` is proved by the published
theorem `rationalCorrectedGradedTransitionStatement`
(`RationalCorrectedGradedTransitionProof`). Given proofs of the other inputs,
the target follows in either of two ways:

* apply `rationalSharpClassFormula_of_open` (or
  `rationalSharpClassFormula_of_association`) to their proofs;
* apply `rationalSharpClassFormulaReduction` to their proofs.

## Dependency ledger

The conditional theorems themselves invoke no Langlands classification, no
character-independence result, no geometric-lemma result and no adjointness
theorem.

The published `rationalBruhat` and `dynamicParabolicQuotientCompact` are
structural: Borel–Tits 5.15, and compactness of `P(k)\G(k)`.

The published `rationalCorrectedGradedTransitionStatement` is assembled from:

* parabolic quotient compactness;
* the surviving-support and orbit-radical theorems;
* the standard-parabolic points theorem;
* the squared-modulus theorem.

Its own Markdown records a recursive constant scan of its closure. The closure
reaches no Langlands classification, no character independence of
representations, no geometric-lemma `K0` expansion and no induction/Jacquet
adjointness.

The final theorem `rationalSharpClassFormulaReduction` only applies
`rationalSharpClassFormula_of_open`, so it adds no dependency.
