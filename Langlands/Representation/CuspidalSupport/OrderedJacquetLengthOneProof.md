# Proof of the ordered length-one Jacquet criterion

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

The development check reported no diagnostics.
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
`CuspidalSupport` modules are the target statement and the evaluation module
`InducedJacquetEvaluation`. A text search of all 77 files finds no occurrence of
`Segment`, `segment`, `Multisegment`, `Derivative`, `derivative`,
`SquareIntegrable`, `Tempered`, `Classification`, `Socle`, `socle` or
`Uniqueness`. The single hit for `Exhaustion` is
`UnipotentExhaustionClause` in `Parabolic.GeometricPrerequisitesStatement`,
a geometric clause about compact open subgroups of the unipotent radical. It
is not a representation exhaustion theorem. In particular, the closure
contains none of the following excluded declarations:
`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
`SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`,
`SegmentSpecialEssentialSquareIntegrability`,
`SquareIntegrableLanglandsClassification`,
`GenericSegmentProductUniqueness`, `OrderedMultisegmentSocleExistence`,
`MultisegmentSocleExhaustion` and `SegmentSocleProductIrreducibility`. It
also excludes the separate submodule uniqueness criterion
`Langlands.LengthTwoUniqueSubrepresentationCriterion`
(`Filtration.LengthTwoUniqueSubrepresentationStatement`) and its proof module.

`CuspidalSupport.InducedJacquetEvaluation` is the module for the
two-block cuspidal-induction argument. `Filtration.MultiplicityAdditivityProof`,
`Filtration.IrreducibleMultiplicityProof`, `Filtration.MultiplicityIndependenceProof`
and `Filtration.MultiplicityTransportProof` were proved alongside results with
other main goals: tempered quotient reflection and a supported Jacquet
comparison. Only these general Jordan–Hölder multiplicity modules are imported
here, not those main conclusions. The import closures of those modules are part
of the list above.

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
one of the excluded declarations or a consequence of them. The proof
uses no derivative formula (Ze80 §3.5 or §9.6, or BZ77), no segment product
irreducibility criterion (Ze80 4.2 or 9.7), no analytic result (Ze80 9.3),
and no segment endpoint or segment Jacquet conclusion. It does not use
Frobenius reciprocity. The nonzero map out of the Jacquet module is built
directly by evaluation.
