# Inputs for the signed class formula on the actual rational points

Module `Langlands.Representation.Aubert.General.RationalSharpClassFormulaInputs`.

Authors:

* Worker 751: the first assembly.
* Worker 4217: the reduced-input corollaries. Workers 751 and 4217 wrote these
  for Library `3f0bcbd4638c9c42befdc9f7e1578d62fde2c959` and updated them for
  Library `e449cde988d4e97ab280b8d4d11262887ccc26e0`. They are in the shared
  draft of Task 4217 (`13e2abdc-2be7-4191-b74b-9eae99a56fcc`).
* Worker 29, with coauthor Worker 3640 (Task 3640): the final theorem
  `rationalSharpClassFormulaReduction`. Worker 29 also rechecked the module
  against Library `3489c50380b46cfbdad8997457a217e6e8e6a27d`, which
  contains the published statement module
  [`RationalSharpReductionStatements`](RationalSharpReductionStatements.md).
* Worker 442 (proof task `18c36a7c-1b08-4443-b90a-38a4f0b9532a`) rechecked
  the unchanged Lean module against Library
  `c40a01345b2f4172fa41e07ff31644b40e695003` and submitted it. In
  environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` the module has zero
  errors and zero warnings, and the final theorem uses only the axioms
  `propext`, `Classical.choice` and `Quot.sound` (development check
  `f74b9c9f-a981-4f9e-bb15-99bf4e8a5dd0`).

The module uses:

* Worker 1511's generic reduction
  `Langlands.Aubert.General.SharpClassFormula.class_formula_of_exact`, from
  `SharpClassFormulaReduction`;
* Worker 691's endpoint-free conditional exactness theorem
  `RationalPointFamily.rationalIsExactBeforeTerminal_of_inputs`, from
  `RationalCorrectedExactnessReduction`.

The module is conditional and does not prove the target. It proves the
published reduction proposition
`RationalPointFamily.RationalSharpClassFormulaReductionStatement`, which says:
the target `RationalPointFamily.RationalSharpClassFormulaStatement` follows
from four propositions that the Library states but does not yet prove. The
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

## Remaining inputs and owners

Library `c40a0134…` proves none of the following. For two of them it has
only conditional reductions:
`rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
and `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`.

| Input | Owner task |
| --- | --- |
| `RationalCorrectedGradedVanishingStatement` | `277860be-2aeb-4a85-8ccb-f1e2e5c573b9` |
| `RationalSupportCategoryInductionJacquetStatement` | `09268952-5848-4585-90e4-0a12121c60ef` |
| `RationalSupportCategoryExactnessDetectionStatement` | `d70a1edd-5a84-4b03-aecf-2818901809d4` |
| `RationalSupportCategoryJacquetVanishingStatement` | `bc64458d-2bc4-438a-9992-ba06185affa7` |
| or `RationalCuspidalSupportAssociationStatement` | `fc414cb1-5832-4033-a2aa-d7c27f5e4691` |

`RationalCorrectedGradedTransitionStatement` is proved by the published
theorem `rationalCorrectedGradedTransitionStatement`
(`RationalCorrectedGradedTransitionProof`). Once the other inputs are
published, the target follows in either of two ways:

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
`rationalSharpClassFormula_of_open`, so it adds no dependency. Whoever reuses
the proofs of the remaining inputs must record their dependencies at that
point.
