# Proof of the ordered length-one Jacquet criterion

Authors: Worker 163 wrote the Lean proof (shared draft revision 1 of task
`ac7b8f7b-65ee-4cee-b666-821fdadf6621`, reused unchanged); Worker 949 added
the import and dependency audit below for proof task
`75b721bc-75ee-400d-9673-a24fe85ef1eb`.

## What is proved

The theorem
`Langlands.CuspidalSupport.normalizedJacquetOrderedLengthOneCriterion`
has exactly the type
`NormalizedJacquetOrderedLengthOneCriterion.{uF, uA, uW, uZ}` from
`Langlands.Representation.CuspidalSupport.OrderedJacquetLengthOneStatement`.
Its four universes (field, ambient carrier, and the two Levi target carriers)
are independent level parameters, and it has no outer hypotheses. The proof
introduces exactly the proposition's quantified data and premises. It proves
the two conclusions: the normalized Jacquet module of the actual
subrepresentation `S` is equivalent to `σ`, and that of the actual quotient
`A / S` is equivalent to `τ`. It does not prove any of the premises; the
statement Markdown explains how the premises relate to Zelevinsky 1980
Proposition 1.11(b), and an application to actual parabolic induction must
still prove them.

## The implemented proof

Write `X`, `R` and `Y` for the normalized Jacquet representations of
`SmoothRep.subrepresentation A S`, of `A` and of `SmoothRep.quotient A S`.

1. *Irreducibility.* `repLength_eq_one_iff` turns the two `repLength = 1`
   premises into `X.IsIrreducible` and `Y.IsIrreducible`.
2. *First equivalence.* `jacquetEvaluation T B f` takes the supplied map `f`
   into `T.normalizedParabolicInduced B σ` to an intertwiner `X → σ`. It
   evaluates at the identity and descends to the normalized Jacquet module.
   The positive induction half modulus cancels the inverse Jacquet half
   modulus, so the target is exactly `σ`. `jacquetEvaluation_ne_zero` shows
   it is nonzero because `f ≠ 0`. Mathlib's Schur lemma
   `Representation.IsIrreducible.bijective_or_eq_zero`, applied to the
   irreducible `X` and `σ`, makes it bijective, and
   `IntertwiningMap.ofBijective` gives an actual `Representation.Equiv`
   `e : X ≃ σ`.
3. *`X` is not equivalent to `τ`.* An equivalence `X ≃ τ` composed with
   `e.symm` would give `σ ≃ τ`, contradicting the inequivalence premise.
4. *Exactness.* The canonical inclusion `SmoothRep.subtype A S` and
   projection `SmoothRep.mkQ A S` are injective and surjective
   (`SmoothRep.subtype_injective`, `SmoothRep.mkQ_surjective`). The range of
   the first equals the kernel of the second (`Submodule.range_subtype`,
   `Submodule.ker_mkQ`). `T.normalizedJacquetMap_exact` carries this actual
   short exact sequence to an exact sequence `X → R → Y` of normalized
   Jacquet modules, with injective first map and surjective second map.
5. *Splitting the multiplicity.* `jordanHolderShortExactDecomposition`,
   applied to that sequence and to the premise
   `HasJordanHolderMultiplicity (Rep.of R) (Rep.of τ) 1`, gives
   multiplicities `mX` of `τ` in `X` and `mY` of `τ` in `Y` with
   `mX + mY = 1`.
6. *Second equivalence.* For an irreducible representation,
   `IrreducibleMultiplicityProof.multiplicity` says the multiplicity of `τ`
   is `1` if it is equivalent to `τ` and `0` otherwise. By step 3, `mX = 0`,
   so `mY = 1`. Applying the same theorem to the irreducible `Y` gives an
   actual equivalence `Y ≃ τ`.

The development check (`lean_check` `ed2bfb72-aba3-4b60-9d28-c93d4216afdd`,
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`) reported no diagnostics.
It found the level parameters `uF uA uW uZ` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Import audit

The module directly imports the statement module and four published modules:
`CuspidalSupport.InducedJacquetEvaluation`,
`Parabolic.NormalizedJacquetExactnessProof`,
`Filtration.MultiplicityAdditivityProof` and
`Filtration.IrreducibleMultiplicityProof` (all under
`Langlands.Representation`). Following every `import Langlands...` line
transitively gives this complete project import closure of 77 modules:

- `Langlands.Representation.CuspidalSupport`:
  `OrderedJacquetLengthOneStatement`, `InducedJacquetEvaluation`.
- `Langlands.Representation.Parabolic`: `NormalizedJacquetExactnessProof`,
  `NormalizedJacquetStatement`, `UnipotentFiniteContainment`,
  `LeviBridges`, `GeometricPrerequisitesStatement`.
- `Langlands.Representation.Filtration`: `Definitions`,
  `ObjectDefinitions`, `RepresentationLength`, `MultiplicityStatement`,
  `MultiplicityAdditivityStatement`, `MultiplicityAdditivityProof`,
  `IrreducibleMultiplicityStatement`, `IrreducibleMultiplicityProof`,
  `MultiplicityIndependenceProof`, `MultiplicityTransportStatement`,
  `MultiplicityTransportProof`, `GradedRefinementStatement`,
  `GradedRefinementProof`, `IntervalLiftStatement`, `IntervalLiftProof`,
  `LengthCriterionStatement`, `LengthCriterionProof`,
  `LengthTwoMatchingStatement`, `LengthTwoMatching`,
  `JordanHolderStatement`, `JordanHolderComparisonProof`,
  `JordanHolderTransportProof`.
- `Langlands.Representation.Jacquet`: `Coinvariants`, `PositiveCharacter`,
  `SmoothTwist`, `Normalized`, `Parabolic`, `ExactStatement`, `ExactProof`.
- `Langlands.Representation.Induction`: `Definitions`, `Parabolic`.
- `Langlands.Representation.Category`: `Basic`, `Subquotients`.
- `Langlands.Representation.Smooth`: `Definitions`,
  `SmoothPart.Definitions`, `Transfer.PullbackStatement`,
  `Transfer.PullbackProof`, `Transfer.SubquotientStatement`,
  `Transfer.SubquotientProof`.
- `Langlands.Representation.Compact`: `FiniteMean`, `Definitions`,
  `OrbitMeanTranslation`, `ProjectionStatement`, `ProjectionProof`.
- `Langlands.Representation.Twist`: `Definitions`, `SmoothStatement`,
  `SmoothProof`.
- `Langlands.Representation.Geometric`: `WeylDefinitions`,
  `RefinementDefinitions`.
- `Langlands.Representation.Conductor.Congruence`.
- `Langlands.Representation.RankinSelberg`: `Measures`,
  `UnimodularityStatement`, `UnipotentUnimodularity`.
- `Langlands.Group.GL`: `Basic`, `Blocks`, `OppositeBlocks`, `Padic`,
  `PadicBlocks`, `Maps`, `UpperUnipotent`, `NormalizedCharacter`,
  `BlockModulus`, `BlockIwahoriDefinitions`.
- `Langlands.LocalField`: `Definitions`, `Canonical`, `Topology`,
  `Normalization.Definitions`, `Normalization.Statement`,
  `Normalization.Proof`.
- `Langlands.HarmonicAnalysis.Basic`.

All other imports are Mathlib modules or `Lean.Elab.Tactic.Omega`. No module
in the closure lies under
`Langlands.Representation.Classification`, where the segment, multisegment,
classification and exhaustion declarations live. The only
`CuspidalSupport` modules are the target statement and Worker 241's
evaluation module. A text search of all 77 files finds no occurrence of
`Segment`, `segment`, `Multisegment`, `Derivative`, `derivative`,
`SquareIntegrable`, `Tempered`, `Classification`, `Socle`, `socle` or
`Uniqueness`. The single hit for `Exhaustion` is
`UnipotentExhaustionClause` in `Parabolic.GeometricPrerequisitesStatement`,
a geometric clause about compact open subgroups of the unipotent radical. It
is not a representation exhaustion theorem. In particular, the closure
contains none of the declarations named by the task's exclusions:
`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
`SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`,
`SegmentSpecialEssentialSquareIntegrability`,
`SquareIntegrableLanglandsClassification`,
`GenericSegmentProductUniqueness`, `OrderedMultisegmentSocleExistence`,
`MultisegmentSocleExhaustion` and `SegmentSocleProductIrreducibility`. It
also excludes the separate submodule uniqueness criterion
`Langlands.LengthTwoUniqueSubrepresentationCriterion`
(`Filtration.LengthTwoUniqueSubrepresentationStatement`, statement candidate
`0424e40d-f917-4b35-8892-a621828e3a09`) and its proof module.

The accepted artifact records that place the closure's proof modules in the
Library name these producing tasks:

| Module(s) | Producing task |
| --- | --- |
| `Parabolic.NormalizedJacquetExactnessProof` | `9d580fe5-0589-4dfa-9506-1010e413a529` |
| `Jacquet.ExactProof` | `d30fdbfc-1ea3-4554-9b0f-540abe813aea` |
| `Parabolic.UnipotentFiniteContainment` | `cba1f5ba-df9a-4ee7-a403-baaeebbf4d63` |
| `RankinSelberg.UnipotentUnimodularity` | `4ad92be9-9115-4e7d-b42a-b2adc7dde3e5` |
| `Filtration.MultiplicityAdditivityProof`, `Filtration.IrreducibleMultiplicityProof`, `Filtration.MultiplicityIndependenceProof` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Filtration.MultiplicityTransportProof` | `b8ecf398-d8ff-48bd-a6b3-5da6557b7655` |
| `Filtration.JordanHolderComparisonProof` | `b43fcaf9-8be5-4717-a87b-a84c667efcbe` |
| `Filtration.JordanHolderTransportProof` | `77ffbd6e-17db-4751-8dee-c6dcb3b92e09` |
| `Filtration.GradedRefinementProof` | `8f135e79-b688-4075-b8e6-b05a81a36883` |
| `Filtration.IntervalLiftProof` | `58e0544d-0db2-42f5-8d39-79d38ff5e2cd` |
| `Filtration.LengthCriterionProof` | `8520a63d-88a5-45e7-adef-84849528ad9d` |
| `Filtration.LengthTwoMatching` | `53969569-6b54-45b3-a1f8-89f1fe96a1f8` |

`CuspidalSupport.InducedJacquetEvaluation` is Worker 241's module for the
two-block cuspidal-induction argument. None of these tasks is on the
exclusion list. Tasks `9f88af41-d438-475e-ae54-6ef33bcfb8ed` and
`b8ecf398-d8ff-48bd-a6b3-5da6557b7655` have other main goals: tempered
quotient reflection and a supported Jacquet comparison. Only their general
Jordan–Hölder multiplicity modules are imported here, not their main
conclusions. The import closures of those modules are part of the list above.

## Mathematical dependency audit

The proof uses only these results:

- `repLength_eq_one_iff` (`Filtration.RepresentationLength`): composition
  length one is irreducibility.
- `jacquetEvaluation` and `jacquetEvaluation_ne_zero`
  (`CuspidalSupport.InducedJacquetEvaluation`): evaluation at the identity
  for a map into normalized parabolic induction.
- `SmoothRep.subtype_injective` and `SmoothRep.mkQ_surjective`
  (`Category.Subquotients`): the actual subrepresentation and quotient.
- `normalizedJacquetMap_exact`
  (`Parabolic.NormalizedJacquetExactnessProof`): exactness of the normalized
  Jacquet functor.
- `jordanHolderShortExactDecomposition`
  (`Filtration.MultiplicityAdditivityProof`): Jordan–Hölder multiplicity is
  additive on short exact sequences.
- `IrreducibleMultiplicityProof.multiplicity`
  (`Filtration.IrreducibleMultiplicityProof`): the multiplicity of `τ` in an
  irreducible representation.
- Mathlib's `Representation.IsIrreducible.bijective_or_eq_zero`,
  `Representation.IntertwiningMap.ofBijective`,
  `Representation.Equiv.symm`/`trans`, `Submodule.range_subtype` and
  `Submodule.ker_mkQ`, and the `omega` decision procedure.

These are general facts about smooth representations, the Jacquet functor
and composition series. None of them is a segment, multisegment, derivative,
square-integrability, tempered, classification or exhaustion result. None is
one of the excluded tasks' conclusions or a consequence of them. The proof
uses no derivative formula (Ze80 §3.5 or §9.6, or BZ77), no segment product
irreducibility criterion (Ze80 4.2 or 9.7), no analytic result (Ze80 9.3),
and no segment endpoint or segment Jacquet conclusion. It does not use
Frobenius reciprocity. The nonzero map out of the Jacquet module is built
directly by evaluation.
