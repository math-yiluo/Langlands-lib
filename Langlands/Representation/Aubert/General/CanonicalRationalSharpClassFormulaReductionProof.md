# Proof of the reduction of the canonical Sharp class formula

Module `Langlands.Representation.Aubert.General.CanonicalRationalSharpClassFormulaReductionProof`.

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalSharpClassFormulaReductionStatement`
(module `CanonicalRationalComplexReductionStatements`) at its universe
parameters `u`, `v`:

```lean
theorem canonicalRationalSharpClassFormulaReduction :
    CanonicalRationalSharpClassFormulaReductionStatement.{u, v}
```

The statement is the curried implication

```lean
CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
  RationalCorrectedGradedVanishingStatement.{u, v} →
    CanonicalRationalSharpClassFormulaStatement.{u, v}
```

That is, Renard VI.3.5 (the whole-category cuspidal splitting, at carrier
universe `max (u + 1) v`) and the corrected graded vanishing target imply the
signed class formula `D_G([E]) = (-1)^{|I|} [E#]` of Aubert 1995,
Corollaire 3.9 (a), on the canonical actual support category. The statement,
its meaning and its literature provenance are described in
`CanonicalRationalComplexReductionStatements.md`; this file describes only the
Lean proof.

The theorem is stated with the published proposition as its type, unchanged.
The two inputs are taken as hypotheses and are neither proved nor weakened. No
premise is added. Every other input of the intermediate steps below is
discharged from the two hypotheses or from proved Library theorems.

Authors: Worker 29, with Worker 3640 (Task 3640, block (iii)), who wrote the
proof; Worker 446 (Task 6558) checked it, made the imports explicit and
rewrote this Markdown.

## Proof

The tactic proof introduces `hwhole` (the whole-category splitting, at
`.{u, max (u + 1) v}`) and `hvan` (corrected graded vanishing, at `.{u, v}`).
All intermediate propositions are at `.{u, v}` unless stated otherwise. All
modules named below are in `Langlands/Representation/Aubert/General/` unless
stated otherwise.

1. Cuspidal Jacquet-factor extraction (`hextract`).
   `rationalCuspidalExtractionInputs_of_wholeStatement hwhole`
   (module `RationalLeviInductionExclusionFromWhole`) gives
   `RationalCuspidalExtractionInputsStatement`, and
   `rationalCuspidalJacquetFactorExtraction_of_inputs`
   (module `RationalCuspidalExtractionInputs`) turns it into
   `RationalCuspidalJacquetFactorExtractionStatement`.
2. Association of cuspidal supports (`hassoc`).
   `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction hextract`
   (module `RationalCuspidalSupportAssociationReduction`) gives
   `RationalCuspidalSupportAssociationStatement`.
3. Stability of the support categories under the induction-Jacquet
   composites (`hind`).
   `rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
   (module `SupportCategoryInductionJacquetReduction`) takes three arguments:
   - `rationalSupportCategoryDecomposition_of_wholeStatement hwhole`
     (module `RationalSupportCategoryDecompositionFromWhole`), the support
     decomposition `RationalSupportCategoryDecompositionStatement`;
   - `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement hwhole`
     at universes `.{u, max (u + 1) v}` (module
     `Langlands/Representation/CuspidalSupport/RationalCuspidalInducedEmbeddingFromWhole`),
     the Levi cuspidal/remainder splitting
     `RationalLeviJacquetCuspidalRemainderSplittingStatement.{u, max (u + 1) v}`.
     This is the universe the consumer requires, and it equals the carrier
     universe of `hwhole`, so no universe changes;
   - `hassoc`.

   The result is `RationalSupportCategoryInductionJacquetStatement`.
4. Exactness detection on the support categories (`hdet`).
   `rationalSupportCategoryZeroDetectionReduction`
   (module `RationalSupportCategoryZeroDetectionProof`) proves the published
   `RationalSupportCategoryZeroDetectionReductionStatement`; applied to
   `hextract` it gives `RationalSupportCategoryZeroDetectionStatement`.
   `rationalSupportCategoryExactnessDetectionReduction`
   (module `RationalSupportCategoryExactnessReduction`) proves the published
   `RationalSupportCategoryExactnessDetectionReductionStatement`; applied to
   the previous result it gives `RationalSupportCategoryExactnessDetectionStatement`.
   Both reduction statements are in `RationalDetectionFiniteLengthReductionStatements`.
5. Jacquet vanishing along Levis containing no associate of the support
   (`hjv`).
   `rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
   (module `RationalJacquetVanishingFromDynamicCompactness`) takes the proved
   quotient compactness `Langlands.BruhatTits.dynamicParabolicQuotientCompact`
   (module `Langlands/BruhatTits/Parabolic/QuotientCompactProof`, at `.{u}`)
   and `hassoc`. It gives `RationalSupportCategoryJacquetVanishingStatement`.
6. The rational class formula.
   `rationalSharpClassFormulaReduction` (module
   `RationalSharpClassFormulaInputs`) proves the published
   `RationalSharpClassFormulaReductionStatement`
   (module `RationalSharpReductionStatements`), whose four inputs are, in
   order, corrected graded vanishing, induction-Jacquet stability, exactness
   detection and Jacquet vanishing. Applied to `hvan`, `hind`, `hdet` and
   `hjv`, it gives `RationalSharpClassFormulaStatement`.
7. The canonical form.
   `canonicalRationalSharpClassFormula_of_rational` (module
   `CanonicalRationalComplexTargetBridgesProof`) shows that
   `RationalSharpClassFormulaStatement` implies
   `CanonicalRationalSharpClassFormulaStatement`, by instantiating the
   structural premises of the former at the published canonical data. Applied
   to step 6, it closes the goal.

The finite-length premise on `E#` that the class formula needs is not
concluded anywhere in this chain: it stays a premise inside the unchanged
conclusion, as in `SharpClassFormulaTarget`.

## Inputs from proof tasks

Steps 4, 6 and 7 use theorems of four modules that are the proofs of other
proof tasks:

- `RationalSupportCategoryZeroDetectionProof`, Task 6582
  (`f7b6068d-c312-487a-b08f-72f5382bd5fb`);
- `RationalSupportCategoryExactnessReduction`, Task 6583
  (`e9fddf52-5367-4151-a290-413d98622e89`);
- `RationalSharpClassFormulaInputs`, Task 6483
  (`18c36a7c-1b08-4443-b90a-38a4f0b9532a`);
- `CanonicalRationalComplexTargetBridgesProof`, Task 6425
  (`d7477c1e-06c2-43ec-9035-3eb6b594058b`).

All four modules have been reviewed and are in Library commit
`457e31a2131a1083c26931d33fec09a71fea54d6`. This proof imports them by
Lean name.

## Check

Against that Library commit, the module compiles in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` with zero errors and zero warnings.
The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
