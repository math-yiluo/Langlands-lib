# Proof of the reduction of canonical Sharp irreducibility

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalSharpIrreducibleReductionStatement`
(module `CanonicalRationalSharpReductionStatements`) at universes `u`, `v`:

`theorem canonicalRationalSharpIrreducibleReduction :
  CanonicalRationalSharpIrreducibleReductionStatement.{u, v}`.

That is, the five inputs

- Renard VI.3.5
  (`CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`),
- `RationalCorrectedGradedVanishingStatement.{u, v}`,
- `DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}`,
- `DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`,
- `RationalInducedK0WeylConjugacyStatement.{u, v}`,

in this order, imply `CanonicalRationalSharpIrreducibleStatement.{u, v}`,
Aubert 1995, Corollaire 3.9 (b), for the canonical actual families. The
statement, its meaning and its provenance are described in the statement
module's Markdown. This file describes only the Lean proof. The proof uses no
hypothesis beyond the statement's five inputs.

This is a derived, internal composition of whole published propositions. Its
literature interpretation is inherited from
`CanonicalRationalSharpReductionStatements.md` and the imported target
modules; it introduces no new translation of the sources. In particular, it
proves the reduction rather than the unconditional irreducibility target.

The field universe `u` and representation universe `v` remain independent.
The first, third and fourth inputs have carrier universe `max (u + 1) v`.
Every field, connected reductive group, maximal split torus, generic
cocharacter, topology and instance binder remains inside its unchanged
proposition. The canonical conclusion therefore retains all its scope,
including positive characteristic and the empty simple-root type.

## Proof

The tactic proof introduces `hwhole`, `hvan`, `hiDyn`, `hrDyn` and `hWeyl`.
It first derives the support-category inputs of the class formula:

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
   step 2.

Then:

6. The Sharp class formula. `rationalSharpClassFormulaReduction` proves the
   published `RationalSharpClassFormulaReductionStatement`
   (`RationalSharpReductionStatements`). Applied to `hvan` and steps 3, 4
   and 5, it gives `RationalSharpClassFormulaStatement.{u, v}`.
7. Induction compatibility.
   `rationalInductionCompatibility_of_expansion_and_inducedWeyl`
   (`RationalInductionK0Assembly`) is applied to the pair of
   `rationalGeometricK0Expansion` (`RationalGeometricK0Expansion`)
   and `hWeyl`. It gives `RationalInductionCompatibilityStatement.{u, v}`.
8. Involutivity of `D_G`.
   `rationalInvolutivityStatement_of_inducedK0WeylConjugacy`
   (`RationalTermTransitivityProof`) applied to `hWeyl` gives
   `RationalInvolutivityStatement.{u, v}`.
9. `rationalSharpIrreducibleStatement_of_inputs`
   (`SharpIrreducibleReduction`) applied to `hiDyn`, `hrDyn` and
   steps 7, 8 and 6 gives `RationalSharpIrreducibleStatement.{u, v}`.
10. `canonicalRationalSharpIrreducible_of_rational`
    (`CanonicalRationalComplexTargetBridgesProof`) specializes the result to
    the canonical structural data.

The class formula (step 6), induction compatibility (step 7) and involutivity
(step 8) are derived inside the proof; none is an input.

All modules named are in `Langlands/Representation/Aubert/General/`, except
`RationalCuspidalInducedEmbeddingFromWhole` (in
`Langlands/Representation/CuspidalSupport/`) and `QuotientCompactProof` (in
`Langlands/BruhatTits/Parabolic/`).

## Reused proofs

The canonical specialization in step 10 is supplied by
`CanonicalRationalComplexTargetBridgesProof`. The class-formula
reduction in step 6 is supplied by `RationalSharpClassFormulaInputs`, which
records its conditional assembly.
Step 4 imports the separate proofs
`RationalSupportCategoryZeroDetectionProof` and
`RationalSupportCategoryExactnessReduction`. Their Markdown
records the conditional zero-detection and exactness-detection assemblies and
the generic reductions they apply.

This module imports those results without reproducing their proofs. Their
statements, the five bottleneck targets, and the unconditional class formula
and irreducibility remain separate. The only new Lean declaration is the theorem of the reduction
proposition named above.
