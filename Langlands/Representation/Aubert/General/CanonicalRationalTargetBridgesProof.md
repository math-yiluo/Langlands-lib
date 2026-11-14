# Proof that existing rational-point Aubert targets imply their canonical forms

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalTargetBridgesStatement`
(module `CanonicalRationalTargetBridgesStatement`) at universes `u`, `v`:

`theorem canonicalRationalTargetBridges : CanonicalRationalTargetBridgesStatement.{u, v}`.

The statement, its meaning and its provenance are described in the statement
module's Markdown. This file describes the Lean proof only. The proof uses no
assumption beyond the statement's own hypotheses.

Authors: Worker 29, with Worker 3640 (Task 3640, Block C(2), bridge proof).
Worker 432 submitted this pair under the proof task Task 6316
(`4320e0f3-a054-4148-bc31-69a2529b0d13`); the Lean source is that task's shared
draft revision 1, unchanged.

## Structure

The module proves eight implications in namespace
`Langlands.Aubert.General.RationalPointFamily`, each with universe parameters
`u` and `v`, of the form

`theorem canonicalRationalX_of_rational (h : RationalXStatement.{u, v}) :
  CanonicalRationalXStatement.{u, v}`.

The final theorem `canonicalRationalTargetBridges` is the anonymous-constructor
tuple of these eight theorems, in the order of the statement's conjuncts:

| Conjunct | Theorem | Existing target (module) | Canonical target |
| --- | --- | --- | --- |
| 1 | `canonicalRationalContragredientCommutation_of_rational` | `RationalContragredientCommutationStatement` (`RationalContragredientTarget`) | `CanonicalRationalContragredientCommutationStatement` |
| 2 | `canonicalRationalInductionCompatibility_of_rational` | `RationalInductionCompatibilityStatement` (`RationalInductionTarget`) | `CanonicalRationalInductionCompatibilityStatement` |
| 3 | `canonicalRationalJacquetCompatibility_of_rational` | `RationalJacquetCompatibilityStatement` (`RationalJacquetTarget`) | `CanonicalRationalJacquetCompatibilityStatement` |
| 4 | `canonicalRationalInvolutivity_of_rational` | `RationalInvolutivityStatement` (`RationalInvolutivityTarget`) | `CanonicalRationalInvolutivityStatement` |
| 5 | `canonicalRationalCuspidalEigenvalue_of_rational` | `RationalCuspidalEigenvalueStatement` (`RationalCuspidalEigenvalueTarget`) | `CanonicalRationalCuspidalEigenvalueStatement` |
| 6 | `canonicalRationalCorollary110a_of_rational` | `RationalCorollary110aStatement` (`RationalCorollaryTargets`) | `CanonicalRationalCorollary110aStatement` |
| 7 | `canonicalRationalCorollary110b_of_rational` | `RationalCorollary110bStatement` (`RationalCorollaryTargets`) | `CanonicalRationalCorollary110bStatement` |
| 8 | `canonicalRationalInducedK0WeylConjugacy_of_rational` | `RationalInducedK0WeylConjugacyStatement` (`RationalInducedWeylConjugacyTarget`) | `CanonicalRationalInducedK0WeylConjugacyStatement` |

All modules named are in `Langlands/Representation/Aubert/General/`. The
canonical targets are in `CanonicalRationalTheorem17Targets`.

## The implemented proof of each implication

Every implication has the same shape: the canonical form is the special case
of the existing target in which every premise is the published canonical one.

The proof introduces the field `k`, its instances, `G`, `hG`, `T`, `i` and
`hi`. It then installs with `let` the instances that the existing target
quantifies over or needs to elaborate:

- `hG.isAffineHom`;
- the canonical `pointTopology` on `RationalPoint k G.X`;
- `IsAffine G.X.left` from `isAffine_of_isAffineHom`;
- `Smooth G.X.hom` from `hG.smooth`;
- `T2Space k` from `BruhatTits.localField_t2Space`;
- `rationalPoint_locallyCompactSpace`;
- `Plancherel.rationalPoints_nonarchimedeanGroup`;
- `rationalPoint_t2Space`;
- `hi.isSplitSubtorus.mono`, except in the induced-Weyl theorem, whose
  statements do not use it.

It introduces `ν`, `hν`, the dynamic hypotheses `hiFl` and `hrFl`
(`DynamicInductionFiniteLengthStatement` and
`DynamicJacquetFiniteLengthStatement` at carrier universe `max (u + 1) v`),
and for conjunct 1 also the per-group hypothesis `hc`. It then applies `h` to
the following published data.

- `hStandard`: `GroupScheme.standardCocharacter`.
- `hRoots`: `GroupScheme.relativeRootSystem k G hG T i hi`. The induced-Weyl
  target has no root-system premise.
- `hU`: `canonicalStandardUnipotent_isClosed hG i ν hi hν`, from the published
  module `CanonicalRationalOperator`.
- `hP`: `standardParabolic_isClosed_of_standardCocharacterStatement`.
- `hproj`: `continuous_standard_projection`.
- `hUc`: `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
- Per-index `hiFl` and `hrFl`: `standardInduction_preservesFiniteLength_of_dynamic`
  and `standardJacquet_preservesFiniteLength_of_dynamic`, applied to the closed
  radicals above and to the global dynamic hypotheses.

The induction, Jacquet and corollary targets also take standard Levi data.
These come from the published `GroupScheme.standardLeviIntersection` (for
`hInter`) and from the published module `CanonicalRationalStructure`:

- `hM`: `canonicalStandardLevi_isClosed`;
- `hLproj`: `canonicalStandardLeviProjection_continuous`;
- `hLUc`: `canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups`;
- `hiLFl` and `hrLFl`: `canonicalStandardLeviInduction_preservesFiniteLength`
  and `canonicalStandardLeviJacquet_preservesFiniteLength`.

The two corollary targets take only `hInter` and `hM` from this list. Their
argument order also differs: `hStandard`, `hInter` and `hRoots` come first,
and `hM` follows `hU`.

The Jacquet target also takes the relative-Weyl data. All are declarations of
`CanonicalRationalStructure`, except the first, which is published in
`GroupScheme`:

- `hConj`: `GroupScheme.standardLeviConjugation`;
- `hN`: `canonicalPointNormalizerComparison`;
- `hZ`: `canonicalPointCentralizerComparison`;
- `CM`: `canonicalCoxeterMatrix`;
- `cs`: `canonicalCoxeterSystem`;
- `hLength`: `canonicalRootLengthComparison`;
- `hSimple`: `canonicalPositiveSimpleReflectionComparison`;
- `hMin`: `canonicalMinimalityLengthCriterion`;
- `hAssoc`: `canonicalAssociatedSubsetLaws`.

The Jacquet theorem also introduces two more binders of the canonical target:
the let-bound finite enumeration `simpleRelativeRootFintype` of the actual
simple roots, and the arbitrary `Fintype (Weyl i)` instance. It then
re-installs the enumeration with `let`, built from the canonical root system,
because instance search does not find the introduced binder. The existing
target, at `hRoots := relativeRootSystem k G hG T i hi`, uses the same
enumeration. The subset `J`, the lift `n` and `hn` stay universally
quantified in the goal; the application of `h` supplies them.

The result of each application is the canonical conclusion up to definitional
unfolding, so `exact` closes the goal. There are two reasons:

- the canonical operator `canonicalRationalAlternatingOperator` (module
  `CanonicalRationalOperator`) and the canonical Levi operator
  `canonicalRationalLeviAlternatingOperator` (module
  `CanonicalRationalStructure`) are defined as the published
  `rationalAlternatingOperator` and `rationalLeviAlternatingOperator` at
  exactly these data (`CanonicalRationalStructure` records this as the `rfl`
  lemmas `rationalAlternatingOperator_eq_canonical` and
  `rationalLeviAlternatingOperator_eq_canonical`);
- the canonical finite-length package `canonicalStandardParabolicFiniteLength`
  and the conjugation-membership proofs are proofs of the same propositions as
  the existing targets' terms, so they agree by proof irrelevance.

The universe levels match: both sides use `{u, v}`, with carriers at
`max (u + 1) v`.

## Scope

The proof shows only that each canonical form is no stronger than its existing
target. It proves no identity of Aubert's paper, no finite-length statement
and no converse implication. A proof of an existing target, composed with the
corresponding conjunct, proves its canonical form.

## Check

`lean_check` of this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` reports zero errors and zero warnings.
The axioms of `canonicalRationalTargetBridges` are `propext`,
`Classical.choice` and `Quot.sound`. Its level parameters are `u` and `v`.

## Provenance

Provenance: derived. The proof relates two families of already published
statements and introduces no new mathematics or translation of the literature.
The literature content of each target and its citations (Aubert 1995,
`aubert-1995-duality`; Ban–Jantzen 2016, `ban-jantzen-2016-duality`) are
recorded in `CanonicalRationalTheorem17Targets.md` and in the existing target
modules.
