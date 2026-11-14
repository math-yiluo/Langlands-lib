# Proof of the reduction of canonical Sharp support retention

This module proves
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalSharpSupportRetentionReductionStatement`
from `CanonicalRationalSharpReductionStatements`, at the independent universe
parameters `u` and `v`:

```lean
theorem canonicalRationalSharpSupportRetentionReduction :
  CanonicalRationalSharpSupportRetentionReductionStatement.{u, v}
```

Its single input is the whole proposition
`CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`.
Its conclusion is the whole
`CanonicalRationalSharpSupportRetentionStatement.{u, v}`: on the canonical
actual rational-point families, the terminal cokernel `E#` of every smooth
`E ∈ Alg({I})` lies in `Alg({I})`.

Proof draft: Worker 29, with Worker 3640 (Task 3640, block (iv)). Submission
preparation and validation: Worker 268.

## Implemented proof

The proof introduces the single hypothesis `hwhole` and composes the following
published reductions.

1. `rationalCuspidalExtractionInputs_of_wholeStatement.{u, v}` applies
   `hwhole` to obtain the extraction inputs.
   `rationalCuspidalJacquetFactorExtraction_of_inputs.{u, v}` then gives
   `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`.
2. `rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction.{u, v}`
   converts this extraction into
   `RationalCuspidalSupportAssociationStatement.{u, v}`.
3. `rationalSupportCategoryDecomposition_of_wholeStatement.{u, v}` gives
   support-category decomposition from `hwhole`, while
   `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`
   at `.{u, max (u + 1) v}` gives the Levi Jacquet cuspidal/remainder splitting
   from the same hypothesis. These two results and step 2 are the three
   arguments of
   `rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association.{u, v}`.
   The result is
   `RationalSupportCategoryInductionJacquetStatement.{u, v}`.
4. `rationalSharpSupportRetention_of_inductionJacquet.{u, v}` gives
   `RationalSharpSupportRetentionStatement.{u, v}`. Its published proof puts
   the terminal-degree object of the standard complex in `Alg({I})` using
   its finite jointly injective family of projections to the induction-Jacquet
   terms, and then uses closure of the support category under the actual
   quotient defining `E#`.
5. `canonicalRationalSharpSupportRetention_of_rational.{u, v}` specializes
   this whole rational target to the published canonical structural data,
   giving exactly the required canonical conclusion.

The imported modules supplying these steps are respectively
`RationalLeviInductionExclusionFromWhole`, `RationalCuspidalExtractionInputs`,
`RationalCuspidalSupportAssociationReduction`,
`RationalSupportCategoryDecompositionFromWhole`,
`RationalCuspidalInducedEmbeddingFromWhole`,
`SupportCategoryInductionJacquetReduction`, `SharpSupportRetentionReduction`
and `CanonicalRationalComplexTargetBridgesProof`. All are in
`Langlands/Representation/Aubert/General/` except
`RationalCuspidalInducedEmbeddingFromWhole`, which is in
`Langlands/Representation/CuspidalSupport/`.

## Scope and provenance

This is an internal proof by composition of existing implications. The
literature interpretation remains the one in
`CanonicalRationalSharpReductionStatements.md`,
`CanonicalRationalComplexTargets.md` and
`RationalWholeCuspidalDecompositionStatement.md`. Those files locate the
underlying definitions and targets in Aubert's 1996 erratum, printed p. 4687
for `Alg({I})` and Remarques (1), printed p. 4690 for `E#`, and Renard VI.3.5,
printed pp. 146–147 for the whole-category decomposition. Support retention
is the derived obligation described in the target documentation; this module
introduces no new translation of a source claim.

The input is used as a hypothesis throughout. The theorem proves the stated
implication and does not discharge the whole-category decomposition. It keeps
the carrier universe `max (u + 1) v` and all quantifiers, topologies and instance
binders of the published input and conclusion. In particular, the conclusion
covers arbitrary smooth representations over every nonarchimedean local field
and every connected reductive group in the target's scope, including an empty
simple-root type. No finite-length or admissibility assumption is added.
The terminal cokernel and its degree `|S| - |I|` are the actual objects fixed by
the canonical target.

The Lean theorem imports the target and the existing proofs without modifying
their statements or implementations. It uses only `propext`,
`Classical.choice` and `Quot.sound`.
