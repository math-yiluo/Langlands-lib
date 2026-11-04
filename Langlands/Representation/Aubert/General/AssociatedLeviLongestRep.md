# The associated-Levi comparison at the inverse longest representative

Author: Worker 757 (task `f7d95940-33d0-49d3-93d6-8d5ff8d89373`).

This module is a conditional (helper) result. It specializes the conditional
assembly `JacquetComplex.associatedLeviComparison_of_survivingStep` (module
`AssociatedLeviSurvivingStep`) to the following data:

* the associated subset `I' = associatedSubset cs I`;
* the inverse longest representative `w = (longestRep cs I)⁻¹`;
* its grade `associatedGrade cs I`;
* the coordinate `associatedCoordinate cs I = S \ I'`.

The Coxeter-combinatorial hypotheses of the assembly are discharged by
`AssociatedLeviSupport`. The orbit Jacquet data are Worker 1255's
`naturalOrbitJacquetData` (module `CorrectedOrbitJacquetNatural`). The module
then derives the published proposition
`TerminalJacquet.AssociatedLeviComparisonStatement` from explicit inputs. It
does not prove the rational target
`RationalPointFamily.RationalAssociatedLeviComparisonStatement`, and it proves
none of the remaining inputs.

Provenance: derived and internal. It assembles display (**) of Aubert's 1996
erratum (p.4690, Remark (1)) along the route described in
`AssociatedLeviSurvivingStep`. Both proofs are single applications of published
or companion results.

## Declarations

* `JacquetComplex.associatedLeviComparison_of_longestRep`. Data: an object
  property `C` of smooth `G`-representations, `I`, `hUc`, and an element
  `n : G` with `hK : x ∈ M I ↔ n⁻¹ x n ∈ M I'`. The Levi data `hMK`, `hLeviK`
  and `hLeviδK` are those of `M I'`. Hypotheses:
  * `hcover : IsBruhatCover T (P ∅) (P I)`;
  * for every `E` with `C E` and every grade `i` with
    `associatedGrade cs I < i < N`: the graded differentials
    `gradedDifferential E I i k` are surjective when
    `k + 1 = Complex.terminalDegree I` (`hsurj`). For terminal degree `1` they
    are injective at `k = 0` (`hinj`), and they are exact at `k` and `k + 1`
    when `k + 2 = Complex.terminalDegree I` (`hex`);
  * `H : SurvivingSupportHypotheses P T cs I (S \ I') (associatedGrade cs I) n`;
  * the compact-limit premise `hNc` for `U_I ∩ P_I`;
  * the structural facts `hS1`, `hS2`, `hr` and `hD07` of
    `naturalOrbitJacquetData`, for `K = I'`, `m = n` and `w`.

  The conclusion is
  `Nonempty (C.ι ⋙ StandardComplex.sharpFunctor I ⋙ r_I ≅ C.ι ⋙ r_{I'} ⋙ LeviComplex.sharpFunctor I' univ ⋙ conjugationFunctor n hK)`.
  It assumes, as `stepGradedMap` does, `[SigmaCompactSpace G]`, `[T2Space G]`,
  compactness of every `G / P_J`, and closedness `hPc` of every `P J`. The
  proof applies `associatedLeviComparison_of_survivingStep` with
  `s0 = associatedCoordinate cs I` and `i0 = associatedGrade cs I`. `hlow`,
  `hconc`, `htop`, `hKs`, `hs` and `hθ` are the corresponding theorems of
  `AssociatedLeviSupport`. The family `DE` is
  `naturalOrbitJacquetData … (C.ι.obj X)`, and its naturality is
  `naturalOrbitJacquetData_isNatural`.
* `TerminalJacquet.associatedLeviComparisonStatement_of_inputs`: the
  published `AssociatedLeviComparisonStatement P M U h hclosed hδ hP hU IsAssociate hM hLevi hLeviδ hPtop hUtop T actual hAssociated`,
  for an actual Coxeter system `actual` on `N_G(T)/Z_G(T)`. Besides the
  statement's own data it assumes `[DecidableEq (Weyl T)]`, the instances and
  `hPc` above, and for every `I`: `hUc I`, `hNc I`, `hr I` and `hcover I`, and
  the graded hypotheses `hsurj`, `hinj` and `hex` on
  `supportObjects … I`. For every `I` and every lift `n` of `longestRep I` it
  also assumes the surviving-support hypotheses `H I n hn`, the facts
  `hS1 I n hn` and `hS2 I n hn`, and `hD07 I n hn hK` for every membership
  equivalence `hK`. Proof: after introducing `I`, `n`, `hn` and the statement's
  `let`s `I'`, `hnM` and `C`, apply
  `associatedLeviComparison_of_longestRep` with `hM I'`, `hLevi I'` and
  `hLeviδ I'`.

## Remaining inputs

The intended rational application must still supply:

* compactness of `G / P_J`, `H`, `hS1`, `hS2` and `hD07`. These are the
  contents of Worker 969's `RationalCorrectedGradedTransitionInputs`. That
  module also derives σ-compactness, closed parabolics and continuity of the
  Levi projections at rational points;
* the Bruhat cover;
* the graded exactness hypotheses on the support category.
