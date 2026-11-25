# Proof of the reduction of canonical Sharp cuspidal-series retention

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalSharpCuspidalSeriesReductionStatement`
(module `CanonicalRationalSharpReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalSharpCuspidalSeriesReduction :
  CanonicalRationalSharpCuspidalSeriesReductionStatement.{u, v}`.

That is, the five inputs

- Renard VI.3.5
  (`CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`),
- `RationalCorrectedGradedVanishingStatement.{u, v}`,
- `DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}`,
- `DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`,
- `RationalInducedK0WeylConjugacyStatement.{u, v}`,

in this order, imply `CanonicalRationalSharpCuspidalSeriesStatement.{u, v}`:
for the canonical actual families, for every standard `I` and every `E` in
the cuspidal series `𝔈(I)`, there are a standard `I'` and an actual point
`n`, related to `I` by the canonical `rootAssociation`, with
`L_{I'} = n L_I n⁻¹` and `E# ∈ 𝔈(I')`. The statement, its meaning and its
provenance are described in the statement module's Markdown. This file
describes only the Lean proof. The proof uses no hypothesis beyond the
statement's five inputs.

## Proof

The tactic proof introduces `hwhole`, `hvan`, `hiDyn`, `hrDyn` and `hWeyl`.
Steps 1–9 derive Sharp irreducibility from the five inputs:

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
6. the Sharp class formula, from `rationalSharpClassFormulaReduction` applied
   to `hvan` and steps 3, 4 and 5;
7. induction compatibility, from
   `rationalInductionCompatibility_of_expansion_and_inducedWeyl` applied to
   the pair of the published `rationalGeometricK0Expansion` and `hWeyl`;
8. involutivity of `D_G`, from
   `rationalInvolutivityStatement_of_inducedK0WeylConjugacy` applied to
   `hWeyl`;
9. Sharp irreducibility, from `rationalSharpIrreducibleStatement_of_inputs`
   applied to `hiDyn`, `hrDyn` and steps 7, 8 and 6.

Then:

10. `rationalSharpSupportRetention_of_inductionJacquet`
    (`SharpSupportRetentionReduction`, published) applied to step 3 gives
    `RationalSharpSupportRetentionStatement.{u, v}`.
11. `rationalSharpCuspidalSeriesReduction` proves the published
    `RationalSharpCuspidalSeriesReductionStatement`
    (`RationalSharpReductionStatements`). Applied to steps 10 and 9, it gives
    `RationalSharpCuspidalSeriesStatement.{u, v}`.
12. `canonicalRationalSharpCuspidalSeries_of_rational`
    (`CanonicalRationalComplexTargetBridgesProof`) specializes the result to
    the canonical structural data.

The class formula, induction compatibility, involutivity, Sharp
irreducibility and support retention are derived inside the proof; none is an
input.

All modules named are in `Langlands/Representation/Aubert/General/`, except
`RationalCuspidalInducedEmbeddingFromWhole` (in
`Langlands/Representation/CuspidalSupport/`) and `QuotientCompactProof` (in
`Langlands/BruhatTits/Parabolic/`). The published theorems of steps 1–9 are
in `RationalLeviInductionExclusionFromWhole`, `RationalCuspidalExtractionInputs`,
`RationalCuspidalSupportAssociationReduction`,
`SupportCategoryInductionJacquetReduction`,
`RationalSupportCategoryDecompositionFromWhole`,
`RationalCuspidalInducedEmbeddingFromWhole`,
`RationalJacquetVanishingFromDynamicCompactness`, `QuotientCompactProof`,
`RationalInductionK0Assembly`, `RationalGeometricK0Expansion`,
`RationalTermTransitivityProof` and `SharpIrreducibleReduction`.

## Published dependencies and scope

The canonical specialization in step 12 uses the published
`CanonicalRationalComplexTargetBridgesProof`; the class-formula
reduction in step 6 uses `RationalSharpClassFormulaInputs`;
and step 11 uses `RationalSharpCuspidalSeriesReduction`.
Step 4 uses the published `RationalSupportCategoryZeroDetectionProof`
and `RationalSupportCategoryExactnessReduction`.
These modules are imported by Lean name, alongside the other published
modules named above.

This result is an internal implication between the published targets. It
adds no translation of the literature and leaves the five input propositions
as hypotheses. In particular, it proves neither those inputs nor
unconditional cuspidal-series retention. The original-source content and
all field, group, topology, instance and carrier-universe binders remain
those of the unchanged statement and its inputs.
