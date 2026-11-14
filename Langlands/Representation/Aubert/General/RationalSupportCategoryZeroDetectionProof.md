# Zero detection on the actual rational-point support categories

Module `Langlands.Representation.Aubert.General.RationalSupportCategoryZeroDetectionProof`.

Authors:

* Worker 4193: the two conditional theorems
  `rationalSupportCategoryZeroDetection_of_irreducibleJacquetDetection` and
  `rationalSupportCategoryZeroDetection_of_cuspidalFactors` and their
  description below, applying the generic reduction of Worker 379
  (`SupportCategoryReductions`). They are reused unchanged from the shared
  draft of Task 4193 (`db02aabd-9901-4fae-9583-ec28c66aec3c`, revision 1).
* Worker 29, with coauthor Worker 3640 (Task 3640): the statement import and
  the final theorem `rationalSupportCategoryZeroDetectionReduction`. Worker 29
  rechecked the module against Library
  `c0debd6f4dd02fdd68d70811cf610906b945a962` together with the statement
  module
  [`RationalDetectionFiniteLengthReductionStatements`](RationalDetectionFiniteLengthReductionStatements.md).
* Worker 261 (Task 6582): checked the conditional assembly against the
  published targets and prepared this proof for independent review.

**Status.** Every theorem in this module is conditional. The module proves
the published reduction proposition
`RationalSupportCategoryZeroDetectionReductionStatement.{u, v}`, which says
that `RationalSupportCategoryZeroDetectionStatement.{u, v}` follows from
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}`. It does not prove
the zero-detection target. The unconditional theorem would apply the first
theorem to a published proof of
`RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}` (proof
task `b7887025-20b3-4c11-9fad-0e70bdf59da6`), or the second to a published
proof of `RationalCuspidalJacquetFactorExtractionStatement.{u, v}` (proof
task `e6add7c5-44c5-45ea-afe9-7f48c98fb927`). Task 4193 owns that theorem;
the input proofs retain their separate owners. The statement program remains
Task 3640 (`46df6a68-5db4-4428-8044-05151d6ce1f6`).

## Statements proved

`rationalSupportCategoryZeroDetection_of_irreducibleJacquetDetection hdet`
takes one premise: the full rational irreducible Jacquet detection proposition
at the same universes `u` and `v`. From it, the theorem proves the full rational
zero-detection proposition `RationalSupportCategoryZeroDetectionStatement.{u, v}`.

`rationalSupportCategoryZeroDetection_of_cuspidalFactors hextract` takes one
premise instead: the full rational cuspidal Jacquet-factor extraction
proposition. From it, the theorem proves the same zero-detection proposition.

`rationalSupportCategoryZeroDetectionReduction` proves the published
proposition `RationalSupportCategoryZeroDetectionReductionStatement.{u, v}`,
that is, the implication
`RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
RationalSupportCategoryZeroDetectionStatement.{u, v}`.

All conclusions are the unchanged published target. Its scope:

* every nonarchimedean local field `k : Type u`, including positive
  characteristic;
* every connected reductive group scheme, including nonsplit and
  non-quasisplit groups, with the literal group `RationalPoint k G.X` at
  `pointTopology`;
* the actual maximal split torus, a generic cocharacter, the literal
  `SimpleRoot i ν` labels, and the actual standard parabolic, Levi and unipotent
  families;
* the displayed premises `hStandard`, `hInter`, `hRoots`, `hN`, `hZ`, closedness
  of the radicals and Levis, local compactness, the nonarchimedean group
  structure and Hausdorffness;
* complex carriers in universe `max (u + 1) v`, with `u` and `v` independent.

Empty simple-root sets and relative rank zero are included. No finite-length,
admissibility, finite-generation, exactness or compact-limit premise is added.
The only extra input is the named detection proposition, or the named
extraction proposition.

## Implemented argument

The first theorem introduces all data and premises of the target. It installs
the same instances as the target:

* the affine instance from `hG.isAffineHom`;
* the monomorphism instance from `hi.isSplitSubtorus.mono`;
* the canonical evaluation topology `pointTopology`;
* the finite simple-root enumeration `simpleRelativeRootFintype`.

It then applies the published generic theorem
`Langlands.Aubert.General.supportCategoryZeroDetection_of_irreducibleJacquetDetection`
at the universes `u`, `u`, `max (u + 1) v`. Its two arguments are supplied as
follows.

1. `hUc`: every standard unipotent subgroup `unipotent i ν J` is a limit of
   compact subgroups. This is proved, not assumed. It is the published
   `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
   applied to the displayed `hStandard`, `hG`, `hi` and `hν`.
2. `hdet`: the generic detection target for the same families. It is the
   premise `hdet` specialized to the same data.

The second theorem composes the first with the published conditional theorem
`rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`
(Worker 658, `RationalIrreducibleJacquetFactorDetection`).

The final theorem is the term
`fun hextract => rationalSupportCategoryZeroDetection_of_cuspidalFactors hextract`.
The intermediate irreducible detection proposition is used inside the proof
and is not an input of the published reduction proposition.

## How the generic reduction works

The published generic proof is by contradiction. Let `E` be in `Alg({I})` with
zero Jacquet modules along every associated standard Levi, and suppose `E` is
nonzero.

* `SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` gives an
  irreducible subquotient `π` of `E`. This works for every smooth
  representation and needs no finite length. It takes the quotient of a cyclic
  subrepresentation by a maximal proper subrepresentation.
* `IsInSupportCategory.of_isSubquotient` puts `π` in `Alg({I})`.
* Detection gives an associated `J` (through some `n`, with both the
  association and the Levi-conjugation condition) such that `r_J(π)` is
  nonzero.
* `jacquet_subsingleton_of_isSubquotient` shows that `r_J(π)` is zero, because
  `r_J(E)` is zero. This lemma uses
  `General.jacquetFunctor_map_isShortExact`, which is proved from
  `Jacquet.Localization.characterLocalizationExactness` under the
  compact-limit hypothesis.

This contradiction finishes the proof.

## Dependencies

The compact-limit proof composes `BruhatTits.dynamicUnipotentCompactOpenContainment`
with `BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups`, through Worker
480's adapter `RationalUnipotentRegularity`. It also uses the existence part
of `hStandard` to identify the standard unipotent subgroup with a dynamic one.

None of the steps listed above applies Langlands classification, character
independence, the geometric lemma or an adjointness theorem. Those
mathematical dependencies enter only through the detection or extraction
proposition, which this module does not prove.

## Sources

The target formalizes the case of one object of the first sentence of the
proof in Aubert's 1996 erratum (printed p. 4687). The input formalizes Renard,
Proposition VI.5.3 (ii), (iii) (printed p. 173), as applied in the proof of
Théorème VI.5.4 (printed p. 174). The reduction is
an internal relation between published targets and adds no literature claim.
The literature content of the targets is recorded in their own Markdown
(`RationalSupportCategoryTargets`, `RationalCuspidalJacquetFactorTarget`) and
in `RationalDetectionFiniteLengthReductionStatements.md`. The target pairs,
the statement pair and every pair they import are unchanged.
