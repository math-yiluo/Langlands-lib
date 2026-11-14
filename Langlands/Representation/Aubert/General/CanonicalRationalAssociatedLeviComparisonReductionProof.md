# Proof of the reduction of the canonical associated-Levi comparison to graded vanishing

Module `Langlands.Representation.Aubert.General.CanonicalRationalAssociatedLeviComparisonReductionProof`.

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalAssociatedLeviComparisonReductionStatement`
(module `CanonicalRationalComplexReductionStatements`) at its universe parameters
`u`, `v`:

```
theorem canonicalRationalAssociatedLeviComparisonReduction :
    CanonicalRationalAssociatedLeviComparisonReductionStatement.{u, v}
```

That is, `RationalCorrectedGradedVanishingStatement.{u, v}` implies
`CanonicalRationalAssociatedLeviComparisonStatement.{u, v}`: display (∗∗) of
Aubert's 1996 erratum (printed p. 4690), the associated-Levi Jacquet comparison
for the canonical actual rational-point families. The statement, its meaning and
its literature provenance are described in the statement module's Markdown
(`CanonicalRationalComplexReductionStatements.md`). This file describes only the
Lean proof. The graded vanishing input is taken as the hypothesis `hvan` and is
neither proved nor weakened; the proof uses no other hypothesis and no axiom
beyond `propext`, `Classical.choice` and `Quot.sound`.

Authors: Worker 29 and Worker 3640 (Task 3640, block (iii)), who wrote the
original draft and the canonical bridge it used; Worker 444 made the proof
self-contained by inlining that bridge.

## Proof

Modules named without a directory are in `Langlands/Representation/Aubert/General/`.
Every declaration used is published in the Library.

1. **The rational target.** Given `hvan`, the published theorem
   `rationalAssociatedLeviComparisonStatement_of_published`
   (`RationalAssociatedLeviReduction`) proves
   `RationalAssociatedLeviComparisonStatement.{u, v}`
   (`RationalTerminalJacquet`) from seven propositions. Six are published
   theorems:
   - `Langlands.GroupScheme.rationalBruhat` (`Langlands/GroupScheme/Rational/RationalBruhatProof`);
   - `Langlands.BruhatTits.dynamicParabolicQuotientCompact`
     (`Langlands/BruhatTits/Parabolic/QuotientCompactProof`);
   - `rationalCorrectedSurvivingSupport` (`RationalCorrectedSurvivingSupportProof`);
   - `rationalCorrectedOrbitRadicalIntersectionStatement`
     (`RationalCorrectedOrbitRadicalProof`);
   - `rationalCorrectedOrbitSquaredModulus` (`RationalCorrectedOrbitModulusProof`);
   - `rationalCorrectedGradedTransitionStatement`
     (`RationalCorrectedGradedTransitionProof`).

   The seventh is `hvan`. Call the result `h`.

2. **Instantiation at the canonical data.** The rational target `h` still takes
   the structural, topological and relative-Weyl facts as explicit premises; the
   canonical target fixes them. After introducing the field `k`, the group `G`,
   the torus `T`, the embedding `i` and `hi`, the proof installs the same local
   instances as the canonical statement (the point topology, affineness,
   smoothness, `T2Space k`, local compactness, the nonarchimedean group structure
   and the Hausdorff property of `RationalPoint k G.X`), introduces the generic
   cocharacter `ν`, `hν` and the two instance binders (the linear order on
   `SimpleRoot i ν` and `Fintype (Weyl i)`), and fixes the `Fintype` instance on
   `SimpleRoot i ν` given by `simpleRelativeRootFintype` for
   `relativeRootSystem k G hG T i hi`, as the canonical statement does. It then
   applies `h` to these objects and to the published canonical data:
   - the `GroupScheme` theorems `standardCocharacter`, `standardParabolicOrder`,
     `standardParabolicEndpoints`, `standardLeviIntersection` and the root
     system `relativeRootSystem k G hG T i hi`;
   - `canonicalStandardUnipotent_isClosed` (`CanonicalRationalOperator`);
     `canonicalPointNormalizerComparison`, `canonicalPointCentralizerComparison`,
     `canonicalStandardLevi_isClosed` and
     `canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups`
     (`CanonicalRationalStructure`);
     `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
     (`RationalUnipotentRegularity`), applied to `standardCocharacter`;
   - from `CanonicalRationalStructure`, the canonical Coxeter matrix and actual
     Coxeter system `canonicalCoxeterMatrix`, `canonicalCoxeterSystem`, and the
     six relative-Weyl facts `canonicalRootLengthComparison`,
     `canonicalPositiveSimpleReflectionComparison`,
     `canonicalLeviWeylIdentification`, `canonicalMinimalityLengthCriterion`,
     `canonicalAssociatedSubsetLaws`, `canonicalAssociatedLeviConjugation`.

   The resulting proposition is, by definition, the body of
   `CanonicalRationalAssociatedLeviComparisonStatement` at these binders, so
   `exact` closes the goal.

Step 2 is the same term as `canonicalRationalAssociatedLeviComparison_of_rational`
in the unpublished draft of Task 6425 (`d7477c1e-06c2-43ec-9035-3eb6b594058b`),
which proves `CanonicalRationalComplexTargetBridgesStatement`. It is written out
here so that this proof depends only on published modules; it does not replace
or prove that bridge statement.
