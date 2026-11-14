# Proof of the reduction of canonical corrected Theorem 3.6

Module `Langlands.Representation.Aubert.General.CanonicalRationalCorrectedTheorem36ReductionProof`.

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalCorrectedTheorem36ReductionStatement`
(module `CanonicalRationalComplexReductionStatements`) at universes `u`, `v`:

```
theorem canonicalRationalCorrectedTheorem36Reduction :
    CanonicalRationalCorrectedTheorem36ReductionStatement.{u, v}
```

The statement says that Renard VI.3.5
(`CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`)
and `RationalCorrectedGradedVanishingStatement.{u, v}` together imply
`CanonicalRationalCorrectedTheorem36Statement.{u, v}`. That conclusion is
corrected Theorem 3.6 (Aubert 1995, with the proof of the 1996 erratum,
printed p. 4687) for the canonical actual complex. The statement Markdown
`CanonicalRationalComplexReductionStatements.md` describes its meaning and
provenance. This file describes only the Lean proof.

The two inputs are hypotheses of the theorem. The proof does not prove either
input, and it uses no hypothesis besides them. Both inputs keep their published
universes. In particular, Renard VI.3.5 is used only at carrier universe
`max (u + 1) v`. The module imports only published modules.

## Authors

- Worker 29, with Worker 3640 (Task 3640, block (iii)), wrote the proof route
  (steps 1–3 and 5 below). Worker 29 also wrote the canonical specialization in
  step 6, which this file transcribes from the shared draft of Task 6425
  (`d7477c1e-06c2-43ec-9035-3eb6b594058b`, theorem
  `canonicalRationalCorrectedTheorem36_of_rational`).
- Worker 4193 wrote step 4a, applying the generic reduction of Worker 379. This
  file transcribes it from the shared draft of Task 6582
  (`f7b6068d-c312-487a-b08f-72f5382bd5fb`), which reuses it from Task 4193.
- Worker 128 wrote step 4b, and Worker 4194 checked it. It applies Worker 499's
  generic exactness reduction. This file transcribes it from the shared draft of
  Task 6583 (`e9fddf52-5367-4151-a290-413d98622e89`), which reuses it from
  Task 4194.
- Worker 445 (Task 6557) inlined steps 4a, 4b and 6 as local steps, so that the
  module depends only on published modules, and wrote this Markdown.

Steps 4a and 4b prove the unconditional conclusions of the published block (ii)
reduction statements `RationalSupportCategoryZeroDetectionReductionStatement`
and `RationalSupportCategoryExactnessDetectionReductionStatement`
(`RationalDetectionFiniteLengthReductionStatements`) from the inputs of this
proof. They are local `have` steps, not public theorems. They do not prove
those statements as Library declarations, and Tasks 6582 and 6583 keep that
work. Step 6 likewise does not prove the bridge statement of Task 6425.

## Proof

The tactic proof introduces `hwhole` (Renard VI.3.5 at `.{u, max (u + 1) v}`)
and `hvan` (graded vanishing). It then proves the following local facts, each
at universes `.{u, v}` unless stated otherwise.

1. **Cuspidal Jacquet-factor extraction** (`hextract`).
   `rationalCuspidalExtractionInputs_of_wholeStatement`
   (`RationalLeviInductionExclusionFromWhole`) derives the extraction inputs
   from `hwhole`. `rationalCuspidalJacquetFactorExtraction_of_inputs`
   (`RationalCuspidalExtractionInputs`) turns them into
   `RationalCuspidalJacquetFactorExtractionStatement`.
2. **Support association** (`hassoc`).
   `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`
   (`RationalCuspidalSupportAssociationReduction`) applied to step 1 gives
   `RationalCuspidalSupportAssociationStatement`.
3. **Induction-Jacquet stability** (`hind`).
   `rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
   (`SupportCategoryInductionJacquetReduction`) takes three arguments:
   - the support-category decomposition
     `rationalSupportCategoryDecomposition_of_wholeStatement hwhole`
     (`RationalSupportCategoryDecompositionFromWhole`);
   - the Levi remainder splitting
     `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement hwhole`
     at `.{u, max (u + 1) v}`
     (`CuspidalSupport/RationalCuspidalInducedEmbeddingFromWhole`);
   - step 2.

   It gives `RationalSupportCategoryInductionJacquetStatement`.
4. **Detection on the support categories.**
   - 4a, zero detection (`hzero : RationalSupportCategoryZeroDetectionStatement`).
     First, `rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
     (Worker 658, `RationalIrreducibleJacquetFactorDetection`) applied to
     step 1 gives the irreducible Jacquet detection proposition `hirr`. Then
     the proof introduces the field, group, torus and the explicit premises of
     the zero-detection target. It installs `pointTopology` on the rational
     points and the finiteness instance
     `simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν`. Finally it
     applies the generic reduction
     `supportCategoryZeroDetection_of_irreducibleJacquetDetection`
     (Worker 379, `SupportCategoryReductions`) to two arguments:
     - the compact-limit property of every standard unipotent subgroup,
       `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
       (Worker 480, `RationalUnipotentRegularity`), proved from the displayed
       standard-cocharacter premise `hStandard`;
     - `hirr` at the same data.
   - 4b, exactness detection
     (`hdet : RationalSupportCategoryExactnessDetectionStatement`). The proof
     introduces the same data and instances as in 4a. It applies
     `ExactnessDetection.supportCategoryExactnessDetection_of_zeroDetection`
     (Worker 499, `SupportCategoryExactnessReduction`) to the same
     compact-limit argument and to `hzero` at the same data.
5. **Corrected Theorem 3.6 with explicit structural premises**
   (`hrat : RationalCorrectedTheorem36Statement`).
   `rationalCorrectedTheorem36_of_inputs` (`RationalCorrectedExactnessReduction`)
   is applied to the structure `RationalCorrectedExactnessInputs` with these
   fields:
   - `bruhat := GroupScheme.rationalBruhat` (`GroupScheme/Rational/RationalBruhatProof`);
   - `gradedVanishing := hvan`;
   - `gradedTransition := rationalCorrectedGradedTransitionStatement`
     (`RationalCorrectedGradedTransitionProof`);
   - `inductionJacquet := hind` (step 3);
   - `exactnessDetection := hdet` (step 4b).
6. **Canonical specialization.** The goal
   `CanonicalRationalCorrectedTheorem36Statement` is introduced up to the
   field, group, torus and maximal split torus `hi`. The proof installs the
   instances that the canonical statement fixes: the point topology, affineness
   and smoothness of `G`, `BruhatTits.localField_t2Space`,
   `rationalPoint_locallyCompactSpace`,
   `Plancherel.rationalPoints_nonarchimedeanGroup` and `rationalPoint_t2Space`.
   It then introduces the generic cocharacter `ν`, the order on simple roots
   and `I`, and applies `hrat` to the published canonical structural data:
   - `standardCocharacter`, `standardParabolicOrder`,
     `standardParabolicEndpoints` and `standardLeviIntersection`;
   - `relativeRootSystem k G hG T i hi`;
   - `canonicalPointNormalizerComparison hG i hi` and
     `canonicalPointCentralizerComparison hG i hi`;
   - `canonicalStandardUnipotent_isClosed hG i ν hi hν` and
     `canonicalStandardLevi_isClosed i ν`;
   - `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
     i ν standardCocharacter hG hi hν`.

   The resulting term has the canonical conclusion's type by definitional
   unfolding.

Unless stated otherwise, every module named is in
`Langlands/Representation/Aubert/General/`. The prefixes `CuspidalSupport/`
and `GroupScheme/Rational/` stand for `Langlands/Representation/CuspidalSupport/`
and `Langlands/GroupScheme/Rational/`.

## Check

The module compiles in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
over Library commit `c40a01345b2f4172fa41e07ff31644b40e695003` with no errors
or warnings and with no `set_option`. The theorem's axioms are `propext`,
`Classical.choice` and `Quot.sound`.
