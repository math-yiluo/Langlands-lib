# Proof of the reduction of the canonical double-Sharp isomorphism

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalSharpInvolutionReductionStatement`
(module `CanonicalRationalSharpReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalSharpInvolutionReduction :
  CanonicalRationalSharpInvolutionReductionStatement.{u, v}`.

That is, the five inputs

- Renard VI.3.5
  (`CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`),
- `RationalCorrectedGradedVanishingStatement.{u, v}`,
- `DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}`,
- `DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`,
- `RationalInducedK0WeylConjugacyStatement.{u, v}`,

in this order, imply `CanonicalRationalSharpInvolutionStatement.{u, v}`,
Aubert 1995, Corollaire 3.9 (c) (`(E#)# ≅ E` on the cuspidal series), for
the canonical actual families. The statement, its meaning and its provenance
are described in the statement module's Markdown. This file describes only
the Lean proof. The proof uses no hypothesis beyond the statement's five
inputs.

## Proof

The tactic proof introduces `hwhole`, `hvan`, `hiDyn`, `hrDyn` and `hWeyl`.
It derives the following whole rational-point propositions, all at `.{u, v}`:

1. extraction, from `rationalCuspidalExtractionInputs_of_wholeStatement` and
   `rationalCuspidalJacquetFactorExtraction_of_inputs`;
2. support association, from
   `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`;
3. induction-Jacquet stability, from
   `rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`,
   applied to `rationalSupportCategoryDecomposition_of_wholeStatement hwhole`,
   to `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement hwhole`
   at `.{u, max (u + 1) v}`, and to step 2;
4. exactness detection, from the reductions
   `rationalSupportCategoryZeroDetectionReduction` and
   `rationalSupportCategoryExactnessDetectionReduction` applied to step 1;
5. support-category Jacquet vanishing, from
   `rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
   applied to the published `BruhatTits.dynamicParabolicQuotientCompact` and
   step 2;
6. the Sharp class formula `RationalSharpClassFormulaStatement.{u, v}`, from
   `rationalSharpClassFormulaReduction` applied to `hvan` and steps 3, 4
   and 5;
7. induction compatibility, from
   `rationalInductionCompatibility_of_expansion_and_inducedWeyl` applied to
   the pair of the published `rationalGeometricK0Expansion` and `hWeyl`;
8. involutivity of `D_G`, `RationalInvolutivityStatement.{u, v}`, from
   `rationalInvolutivityStatement_of_inducedK0WeylConjugacy` applied to
   `hWeyl`;
9. Sharp irreducibility, from `rationalSharpIrreducibleStatement_of_inputs`
   applied to `hiDyn`, `hrDyn` and steps 7, 8 and 6;
10. Sharp support retention, from
    `rationalSharpSupportRetention_of_inductionJacquet` applied to step 3;
11. Sharp cuspidal-series retention
    `RationalSharpCuspidalSeriesStatement.{u, v}`, from
    `rationalSharpCuspidalSeriesReduction` applied to steps 10 and 9.

Then:

12. `rationalSharpInvolutionStatement_of_inputs`
    (`SharpInvolutionReduction`, published) applied to `hiDyn`, `hrDyn` and
    steps 8, 6 and 11 gives `RationalSharpInvolutionStatement.{u, v}`.
13. `canonicalRationalSharpInvolution_of_rational`
    (`CanonicalRationalComplexTargetBridgesProof`) specializes the result to
    the canonical structural data.

The class formula, induction compatibility, involutivity, Sharp
irreducibility, support retention and cuspidal-series retention are derived
inside the proof; none is an input.

The last rational helper produces an actual isomorphism in `SmoothRep`.
Its implementation uses cuspidal-series retention twice to obtain
irreducibility, and hence finite length, of both terminal cokernels. Root
association preserves the cardinality of the indexing subset, so the second
cokernel can be taken at the original degree `|S| - |I|`. Applying the class
formula twice and operator involutivity cancels the two signs. The published
irreducible-class detection theorem then lifts the resulting equality of
exact Grothendieck classes to an isomorphism. The canonical bridge supplies
the canonical structural witnesses without changing the representations or
their degree.

All modules named are in `Langlands/Representation/Aubert/General/`, except
`RationalCuspidalInducedEmbeddingFromWhole` (in
`Langlands/Representation/CuspidalSupport/`) and `QuotientCompactProof` (in
`Langlands/BruhatTits/Parabolic/`). The published theorems of steps 1–10 are
in `RationalLeviInductionExclusionFromWhole`, `RationalCuspidalExtractionInputs`,
`RationalCuspidalSupportAssociationReduction`,
`SupportCategoryInductionJacquetReduction`,
`RationalSupportCategoryDecompositionFromWhole`,
`RationalCuspidalInducedEmbeddingFromWhole`,
`RationalJacquetVanishingFromDynamicCompactness`, `QuotientCompactProof`,
`RationalInductionK0Assembly`, `RationalGeometricK0Expansion`,
`RationalTermTransitivityProof`, `SharpIrreducibleReduction` and
`SharpSupportRetentionReduction`.

## Provenance and dependencies

This is a derived internal composition between published targets. It adds no
translation of the literature. The source meanings of the five inputs and
the conclusion are recorded in the unchanged Markdown paired with
`CanonicalRationalSharpReductionStatements` and
`CanonicalRationalComplexTargets`.

The proof imports the following helper modules:

- step 13 comes from module
  `CanonicalRationalComplexTargetBridgesProof`;
- step 6 comes from module
  `RationalSharpClassFormulaInputs`, using its conditional assembly;
- step 11 comes from module
  `RationalSharpCuspidalSeriesReduction`, using its conditional assembly;
- step 4 comes from modules
  `RationalSupportCategoryZeroDetectionProof` and
  `RationalSupportCategoryExactnessReduction`. These reuse a zero-detection
  assembly with the generic reduction of `SupportCategoryReductions`, and an
  exactness-detection assembly, respectively.

Those modules are imported by their Lean names. This module adds only
the present proof pair and leaves those modules and all
five bottleneck targets unchanged. It proves the five-premise implication;
it does not supply any of the five premises or an unconditional Sharp
involution theorem.
