# Proof that the existing Family 3/4 rational-point targets imply their canonical forms

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.CanonicalRationalComplexTargetBridgesStatement`
(module `CanonicalRationalComplexTargets`) at universes `u`, `v`:

`theorem canonicalRationalComplexTargetBridges :
  CanonicalRationalComplexTargetBridgesStatement.{u, v}`.

The statement, its meaning and its provenance are described in the statement
module's Markdown. This file describes only the Lean proof, which uses no
assumption beyond the hypotheses of the statement.

Authors: Worker 29, with Worker 3640 (Task 3640, block (a), bridge proof).
Submitted unchanged in its Lean by Worker 435 under the proof task Task 6425
(`d7477c1e-06c2-43ec-9035-3eb6b594058b`).

## Structure

The module proves nine implications in namespace
`Langlands.Aubert.General.RationalPointFamily`, each with universe parameters
`u` and `v`, of the form

`theorem canonicalRationalX_of_rational (h : RationalXStatement.{u, v}) :
  CanonicalRationalXStatement.{u, v}`.

The final theorem `canonicalRationalComplexTargetBridges` is the
anonymous-constructor tuple of these nine theorems. They appear in the same
order as the statement's conjuncts:

| Conjunct | Theorem | Existing target (module) | Canonical target |
| --- | --- | --- | --- |
| 1 | `canonicalRationalCorrectedTheorem36_of_rational` | `RationalCorrectedTheorem36Statement` (`RationalCorrectedTheorem36`) | `CanonicalRationalCorrectedTheorem36Statement` |
| 2 | `canonicalRationalFixedLeviComparison_of_rational` | `RationalFixedLeviComparisonStatement` (`RationalTerminalJacquet`) | `CanonicalRationalFixedLeviComparisonStatement` |
| 3 | `canonicalRationalAssociatedLeviComparison_of_rational` | `RationalAssociatedLeviComparisonStatement` (`RationalTerminalJacquet`) | `CanonicalRationalAssociatedLeviComparisonStatement` |
| 4 | `canonicalRationalSharpFiniteLength_of_rational` | `RationalSharpFiniteLengthStatement` (`RationalSharpConsequenceTargets`) | `CanonicalRationalSharpFiniteLengthStatement` |
| 5 | `canonicalRationalSharpClassFormula_of_rational` | `RationalSharpClassFormulaStatement` (`RationalSharpConsequenceTargets`) | `CanonicalRationalSharpClassFormulaStatement` |
| 6 | `canonicalRationalSharpSupportRetention_of_rational` | `RationalSharpSupportRetentionStatement` (`RationalSharpConsequenceTargets`) | `CanonicalRationalSharpSupportRetentionStatement` |
| 7 | `canonicalRationalSharpIrreducible_of_rational` | `RationalSharpIrreducibleStatement` (`RationalSharpConsequenceTargets`) | `CanonicalRationalSharpIrreducibleStatement` |
| 8 | `canonicalRationalSharpCuspidalSeries_of_rational` | `RationalSharpCuspidalSeriesStatement` (`RationalSharpConsequenceTargets`) | `CanonicalRationalSharpCuspidalSeriesStatement` |
| 9 | `canonicalRationalSharpInvolution_of_rational` | `RationalSharpInvolutionStatement` (`RationalSharpConsequenceTargets`) | `CanonicalRationalSharpInvolutionStatement` |

All modules named are in `Langlands/Representation/Aubert/General/`. The
canonical targets are in `CanonicalRationalComplexTargets`.

## The implemented proof of each implication

All nine implications have the same shape. The canonical form is the special
case of the existing target in which every structural premise is the
published canonical value.

### Introduced data and instances

Each proof first introduces the field `k` and its four instances, then `G`,
`hG`, `T`, `i` and `hi`. The canonical statements bind their instances with
`haveI` and `letI` in term mode. These bindings are inlined and are not
binders of the goal, so the proof installs the same instances again with
`let`:

- `hG.isAffineHom`;
- `hi.isSplitSubtorus.mono`;
- the canonical `pointTopology` on `RationalPoint k G.X`;
- `IsAffine G.X.left` from `isAffine_of_isAffineHom`;
- `Smooth G.X.hom` from `hG.smooth`;
- `T2Space k` from `BruhatTits.localField_t2Space`;
- `rationalPoint_locallyCompactSpace k G`;
- `Plancherel.rationalPoints_nonarchimedeanGroup G`;
- `rationalPoint_t2Space k G`.

The existing targets quantify over `LocallyCompactSpace`, `NonarchimedeanGroup`
and `T2Space` on `RationalPoint k G.X` as instance arguments. Instance search
fills them with the last three `let`s above.

The proof then introduces the cocharacter `ν` and `hν`, and the arbitrary
`LinearOrder (SimpleRoot i ν)` of the canonical statement. Conjunct 1 also
introduces the subset `I`. Conjunct 3 also introduces the arbitrary
`Fintype (Weyl i)` instance. The finite enumeration `simpleRelativeRootFintype`
of the canonical statement is a `letI`, so it is inlined too. Every other
quantifier of the canonical conclusion stays in the goal, and the application
of `h` supplies it.

### Applied data

Each proof is `exact h k G hG T i hi ν hν` followed by the canonical value of
each premise of the existing target, in that target's order:

| Premise | Canonical value | Conjuncts |
| --- | --- | --- |
| `hStandard` | `standardCocharacter` | all |
| `hOrder` | `standardParabolicOrder` | all |
| `hEndpoints` | `standardParabolicEndpoints` | 1, 3 |
| `hInter` | `standardLeviIntersection` | all except 4 |
| `hRoots` | `relativeRootSystem k G hG T i hi` | all |
| `hN` | `canonicalPointNormalizerComparison hG i hi` | 1, 2, 3, 5, 6, 8 |
| `hZ` | `canonicalPointCentralizerComparison hG i hi` | 1, 2, 3, 5, 6, 8 |
| `hU` | `canonicalStandardUnipotent_isClosed hG i ν hi hν` | all |
| `hM` | `canonicalStandardLevi_isClosed i ν` | all except 4 |
| `hUc` | `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement i ν standardCocharacter hG hi hν` | all except 2 |
| `hUcLevi` | `canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν` | 2, 3 |

The values `standardCocharacter`, `standardParabolicOrder`,
`standardParabolicEndpoints`, `standardLeviIntersection` and
`relativeRootSystem` are published in namespace `GroupScheme`.
`canonicalStandardUnipotent_isClosed` is in `CanonicalRationalOperator`. The
other `canonical*` values are in `CanonicalRationalStructure`. These are
exactly the values in the canonical-data table of
`CanonicalRationalComplexTargets.md`.

Conjunct 1 then passes the introduced subset `I`. The existing
Theorem 3.6 target takes the order and `I` as instance and explicit
arguments after its premises.

### The associated-Levi comparison

Conjunct 3 needs the actual relative Weyl data as well. After the
introductions, the proof installs with `let` the instance

`simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
  hi.isSplitSubtorus.1 ν : Fintype (SimpleRoot i ν)`.

The published theorems `canonicalAssociatedSubsetLaws` and
`canonicalAssociatedLeviConjugation` take a `Fintype (SimpleRoot i ν)`
instance argument, and instance search does not find the inlined `letI` of
the statement. This is the same enumeration that the existing target uses at
`hRoots := relativeRootSystem k G hG T i hi`. After the premises in the table
above, the proof passes

- `C`: `canonicalCoxeterMatrix hG i hi ν hν`;
- `actual`: `canonicalCoxeterSystem hG i hi ν hν`;
- the five comparison premises: `canonicalRootLengthComparison`,
  `canonicalPositiveSimpleReflectionComparison`,
  `canonicalLeviWeylIdentification`, `canonicalMinimalityLengthCriterion` and
  `canonicalAssociatedSubsetLaws`, each applied to `hG i hi ν hν`;
- `hAssociated`: `canonicalAssociatedLeviConjugation hG i hi ν hν`.

All of these are declarations of `CanonicalRationalStructure`. The
`LinearOrder` and `Fintype (Weyl i)` instance arguments of the existing
target are filled by instance search from the introduced binders.

### Why `exact` closes each goal

The result of each application is the canonical conclusion up to
definitional unfolding. The derived generic arguments (decompositions,
monotonicity, endpoints, unimodularity, `rootAssociation`) are computed
inside the existing target from the supplied premises. The canonical
statement computes them from the same canonical values with the same
functions. Proofs of the same proposition agree by proof irrelevance, so the
only remaining check is that both sides use the same instances and universes.
Both sides use `{u, v}`, with the generic target at `.{u, u, max (u + 1) v}`.

## Scope

The proof shows only that each canonical form is no stronger than its existing
target. It proves no identity of Aubert's paper, no exactness or finite-length
statement and no converse implication. Composing a proof of an existing target
with the corresponding conjunct proves its canonical form. For example, the
published `rationalFixedLeviComparison` (module
`RationalFixedLeviComparisonProof`) with conjunct 2 proves
`CanonicalRationalFixedLeviComparisonStatement`. That composition is not part
of this module.

## Check

`lean_check` of this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, over Library commit
`c40a01345b2f4172fa41e07ff31644b40e695003`, reports zero errors and zero
warnings. The axioms of `canonicalRationalComplexTargetBridges` are `propext`,
`Classical.choice` and `Quot.sound`; its universe parameters are `u` and `v`.

## Provenance

Provenance: derived. The proof relates two families of already published
statements. It introduces no new mathematics and no translation of the
literature. The literature content of each target and its citations (Aubert
1995, `aubert-1995-duality`; Aubert 1996 erratum,
`aubert-1996-duality-erratum`; Ban–Jantzen 2016, `ban-jantzen-2016-duality`)
are recorded in `CanonicalRationalComplexTargets.md` and in the existing
target modules.
