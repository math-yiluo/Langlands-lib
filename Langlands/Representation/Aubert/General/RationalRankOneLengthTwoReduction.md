# Rational rank-one length two from extraction or the whole cuspidal splitting

Author: Worker 3915, Task 3915 (`c53e3363-ffa5-4f01-ae77-aca8e1f49117`).

Module `Langlands.Representation.Aubert.General.RationalRankOneLengthTwoReduction`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

This module reduces the published length-two target
`RationalRankOneLengthTwoStatement.{u, v}` (module
[RationalCorollaryTargets](RationalCorollaryTargets.md)) to a single
unproved proposition. It does **not** prove the target. Each theorem keeps
its input as an explicit hypothesis:

- `RationalCuspidalJacquetFactorExtractionStatement.{u, v}` (module
  [RationalCuspidalJacquetFactorTarget](RationalCuspidalJacquetFactorTarget.md);
  proof task `e6add7c5-44c5-45ea-afe9-7f48c98fb927`), or
- `Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  at universes `u` and `max (u + 1) v`, the whole-category cuspidal splitting of
  Renard VI.3.5 (module
  [RationalWholeCuspidalDecompositionStatement](../../CuspidalSupport/RationalWholeCuspidalDecompositionStatement.md);
  proof task `4bee987a-093b-4054-bd65-7360168351d2`).

Neither proposition is proved in the Library at the time of writing.

The coatom Jacquet-length budget, the other input of the length-two reduction,
is now proved. So it is not a hypothesis here.

## Declarations

`rationalRankOneLengthTwo_of_extraction` assumes
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}` and concludes
`RationalRankOneLengthTwoStatement.{u, v}`. The field universe `u` and the
carrier universe `v` stay independent. The conclusion is the unchanged
published target, with every binder and premise it states. The theorem adds
no other parameter.

`rationalRankOneLengthTwo_of_wholeStatement` assumes
`RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`. This is
the splitting at the carrier universe `max (u + 1) v` of the representations in
the target. The theorem concludes the same `RationalRankOneLengthTwoStatement.{u, v}`.

`rationalRankOneLengthTwoOfExtraction` is the entry declaration. It is a `def`
whose type is the implication
`RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
RationalRankOneLengthTwoStatement.{u, v}`, and its value is
`rationalRankOneLengthTwo_of_extraction`. It has the same content as that
theorem. The `linter.defProp` warning is disabled only for this declaration.

## Proofs

Both proofs are term-mode compositions of published theorems. Neither unfolds
a definition.

`rationalRankOneLengthTwo_of_extraction` applies the published implication
`rationalRankOneLengthTwoFromInputs`
([RationalRankOneLengthInputsProof](RationalRankOneLengthInputsProof.md)).
Its two arguments are as follows.

1. Detection: `rationalMaximalCuspidalJacquetDetectionFromExtraction`
   ([RationalMaximalCuspidalDetectionProof](RationalMaximalCuspidalDetectionProof.md))
   applied to the extraction hypothesis. It gives
   `RationalMaximalCuspidalJacquetDetectionStatement.{u, v}`: every actual
   irreducible subquotient of `i_J σ` has a nontrivial normalized Jacquet
   module for some coatom `univ.erase β`.
2. Budget: the published unconditional `rationalMaximalCuspidalJacquetBudget`
   ([RationalMaximalCuspidalJacquetBudgetProof](RationalMaximalCuspidalJacquetBudgetProof.md)),
   proving `RationalMaximalCuspidalJacquetBudgetStatement.{u, v}`. The sum over
   all coatoms of the composition lengths of the actual normalized Jacquet
   modules of `i_J σ` is at most two.

`rationalRankOneLengthTwo_of_wholeStatement` supplies the extraction hypothesis
of the previous theorem through two published theorems:

1. `rationalCuspidalExtractionInputs_of_wholeStatement`
   ([RationalLeviInductionExclusionFromWhole](RationalLeviInductionExclusionFromWhole.md))
   turns the splitting into `RationalCuspidalExtractionInputsStatement.{u, v}`.
   That proposition holds the actual geometric filtration together with
   proper-standard induction exclusion inside every standard Levi.
2. `rationalCuspidalJacquetFactorExtraction_of_inputs`
   ([RationalCuspidalExtractionInputs](RationalCuspidalExtractionInputs.md))
   turns those inputs into `RationalCuspidalJacquetFactorExtractionStatement.{u, v}`.

## Transitive dependencies

These are recorded as the task asks. The paired Markdown of each module gives
the details.

- Geometric lemma: the budget uses `rationalMaximalSourceGeometricFiltration`.
  The extraction inputs use `exists_pointInducedJacquetGeometricFiltration`.
  Both are proved actual support filtrations of Jacquet modules of standard
  normalized inductions on the rational points. Neither is a hypothesis.
- Adjointness: under the second theorem, proper-induction exclusion uses
  `no_leviCuspidal_subquotient_of_proper_induction_splitting`. That theorem
  uses actual first (Frobenius) adjointness inside each standard Levi.
- Length bound: `rationalRankOneLengthTwoFromInputs` uses
  `exactFamilyLengthBound`, `jacquetFunctor_map_isShortExact`, the compact-limit
  radicals from
  `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`,
  `rationalStandardInductionNonzero` and
  `exists_hasTwoConstituents_of_length_le_two`.
- Weyl data: detection and the budget both obtain the normalizer and
  centralizer comparisons from `rationalWeylComparison`.
- No Langlands classification, Grothendieck-group identity or Aubert
  Proposition 3.2 is used.

The checked axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal composition. The target pair records its provenance:
a derived specialization of the length-two step in Aubert 1995, proof of
Corollary 1.10(b), and Casselman 1995, section 7.1. Detection
follows Renard VI.5.3 and VI.5.4 through cuspidal-factor extraction. That
extraction needs the geometric lemma (VI.5.1) and proper-induction exclusion
(VI.5.2), which the published route derives from VI.3.5. These source
correspondences are recorded and reviewed in the cited modules. This module
introduces no new mathematical assertion beyond the two implications.
