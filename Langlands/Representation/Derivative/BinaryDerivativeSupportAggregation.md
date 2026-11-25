# Actual Leibniz factor constituents and supplied support aggregation

This internal construction selects feasible derivative orders and actual
irreducible factor subquotients for a supplied irreducible constituent of a
binary-product derivative. From supplied support bounds on those factor
constituents, it constructs a support of the original constituent by multiset
addition. It retains the actual invariant subspace, kernel and smooth
isomorphism presenting the constituent in the rank-cast product.

The namespace is `Langlands.Derivative.BinaryDerivativeSupport`. The entry
constructor is `supportData`; the module also contains `FactorData`,
`factorData`, `factorDataOfSubquotient` and `SupportData`.

## Parameters and universes

Fix an arbitrary natural prime `p` with `Fact p.Prime`, a supplied
`F : PadicField.{uF} p`, its supplied `T : F.TopologicalData`, and a supplied
unitary additive character `ψ` for `T.topology`. No particular prime, field,
topological realization or nontrivial-character premise is added.

The universes `uF,uV` remain independent. Throughout this module the actual
representations have carrier universe `max uF uV`:

- `A` is a smooth complex representation of `GL_a(F)`;
- `B` is a smooth complex representation of `GL_b(F)`;
- `D` is a smooth complex representation of `GL_((a+b)-d)(F)`.

All derivatives, extracted constituents and the optional intermediate
subquotient `Q` use this same carrier universe. A general linear derivative
preserves its input carrier universe. Instantiating the published binary
product and extraction constructions at `max uF uV` is legitimate because
`max uF (max uF uV)` reduces to the same maximum.

The multisets in the support constructions have elements
`T.CuspidalDatum.{uV,uF}` in the original base universe `uV`.
The support witnesses therefore supply actual supercuspidal representatives
in that original universe, exactly as required by `IsSupercuspidalSupport`.
There is no resize, carrier lift or inference that an arbitrary
`max uF uV` constituent has such a support. Support existence at that
datum universe is an explicit input.

All ranks are natural numbers. Zero source ranks, zero derivative orders
and zero residual ranks are retained. In particular an actual `GL_0`
carrier is never replaced by a scalar line.

## Actual factor data

`FactorData T ψ A B D` stores a feasible
`x : LeibnizIndex a b d`. Writing `i = x.val.1` and `j = x.val.2`, feasibility
gives `i ≤ a`, `j ≤ b`, `i+j=d`, and the prescribed rank identity

```text
(a-i) + (b-j) = (a+b)-d.
```

It stores actual objects `left : SmoothRep ℂ GL_(a-i)(F)` and
`right : SmoothRep ℂ GL_(b-j)(F)`, proofs that both are irreducible, and
their actual subquotient occurrences in the `i`-th derivative of `A` and
the `j`-th derivative of `B`.

For the literal ambient object

```text
P = rankCast ((left) × (right)),
```

where the product is `T.binaryNormalizedProductFunctor (a-i) (b-j)` and
the cast is `generalLinearRankCast T (leibnizIndices_rank x.property)`,
the data also contains:

- an invariant `subspace` of `P`;
- an invariant `kernel` of the smooth restriction of `P` to `subspace`;
- an actual smooth-category isomorphism
  `occurrenceIso : D ≅ SmoothRep.subquotient P subspace kernel`.

These fields give the constituent-first relation
`SmoothRep.IsSubquotient D P`. They retain an actual quotient presentation,
rather than a class in a Grothendieck group. `FactorData` itself contains
neither an irreducibility proof for `D` nor an assertion that `D` occurs in
the original derivative; its constructors take those premises explicitly.

## The factor-data constructors

`factorData` assumes `hd : d ≤ a+b`, irreducibility of `D`, and an actual
occurrence of `D` in the `d`-th derivative of the binary product of `A,B`.
It also assumes finite length of every feasible-order derivative of each
factor:

```text
∀ i (hi : i ≤ a), (derivative a i hi A).HasFiniteLength,
∀ j (hj : j ≤ b), (derivative b j hj B).HasFiniteLength.
```

It returns `FactorData T ψ A B D`.

The implemented proof first uses the published
`exists_leibnizSmoothPiece_subquotient`. The actual Leibniz filtration and
finite-filtration extraction place `D` in a feasible smooth piece. By the
definition of `leibnizSmoothPiece`, this is exactly the prescribed rank
cast of the binary product of the two factor derivatives.

The private `rankCast_factor_extraction` eliminates the rank equality by
`cases h`. It then applies the published
`T.exists_irreducible_factor_subquotients_of_binaryProduct` to those two
derivatives, using the supplied finite-length hypotheses at the selected
orders. That theorem produces actual irreducible constituents `E,H`,
their occurrences in the derivatives, and the occurrence of `D` in
their product. Its general proof filters the product successively by
composition series of the left and right factors and extracts a grade
twice. Positive ranks use actual induced quotient comparisons; zero ranks
use the actual tensor models.

The private `factorData_nonempty_of_piece` unpacks the resulting
subquotient relation as a subspace, kernel and nonempty isomorphism. These
witnesses assemble a `Nonempty FactorData`. `factorData` uses
`Classical.choice` on this established nonempty type. No canonical choice
or uniqueness is asserted.

`factorDataOfSubquotient` permits an additional supplied
`Q : SmoothRep ℂ GL_(a+b)(F)` and an actual occurrence of `Q` in the binary
product before differentiation. Its premise concerning `D` is an actual
occurrence in the `d`-th derivative of `Q`. All other premises are as
above. It invokes the published
`exists_leibnizSmoothPiece_subquotient_of_subquotient`, retains its
piece-occurrence witness, and applies the same private constructor. The
published extraction theorem uses general derivative exactness to map
the occurrence of `Q`, then actual subquotient transitivity. It also
proves nontriviality of the two derivative factors; this constructor
needs only the piece occurrence and does not store those additional
nontriviality proofs.

## Supplied support aggregation

Let `PL,PR` be arbitrary predicates of type

```text
ℕ → Multiset (T.CuspidalDatum.{uV,uF}) → Prop.
```

`SupportData T ψ A B D PL PR` extends `FactorData T ψ A B D`. It adds
multisets `leftSupport,rightSupport` and the following proofs:

```text
T.IsSupercuspidalSupport left leftSupport,
T.IsSupercuspidalSupport right rightSupport,
PL i leftSupport,
PR j rightSupport,
T.IsSupercuspidalSupport D (leftSupport + rightSupport).
```

The addition is multiset addition, with all repeated entries and their
multiplicities preserved.

`supportData` assumes irreducibility of `D` and supplied
`f : FactorData T ψ A B D`. For every `i ≤ a` and every actual
irreducible subquotient `E` of the `i`-th derivative of `A`, it assumes

```text
∃ s, PL i s ∧ T.IsSupercuspidalSupport E s.
```

It has the corresponding hypothesis with `B,PR,j,H,t`. These are uniform
support hypotheses, not conclusions of this module. `supportData` needs no
separate finite-length premises: those are needed by the preceding
constructors if they are used to supply `f`. It has no explicit `hd`
argument because the feasible index already belongs to `f`.

The proof specializes the two support hypotheses to `f.left` and
`f.right`, using the bounds, irreducibility and actual occurrences stored
in `f`. `Classical.choose` selects their two already supplied support
witnesses. The private `rankCast_binary_support` eliminates the rank
equality and invokes the published `T.binaryProductConstituentSupport`.
The required occurrence of `D` is reconstructed literally from
`f.subspace`, `f.kernel` and `f.occurrenceIso`. This proves that the
selected sum is a support of `D`. The returned structure contains
`toFactorData := f`, both selected multisets, their predicates and their
support witnesses.

The lower support-addition theorem unpacks two supplied cuspidal
presentations, concatenates their actual supercuspidal families, constructs
the actual occurrence of the binary product in that cuspidal induction,
and composes with the supplied occurrence of `D`. Its proof uses general
normalized induction in stages, tensor regrouping, actual product
subquotients and elementary smooth-subquotient transitivity. It assumes
no support-existence or support-uniqueness theorem.

## Provenance and dependency audit

This pair has internal provenance and an empty source list. It composes
already published general derivative, induction and quotient
constructions. It translates no additional external theorem.
Its three direct imports have these roles:

| Module after `Langlands.Representation.` | Used construction |
| --- | --- |
| `Derivative.LeibnizConstituentExtraction` | A feasible actual smooth piece containing `D`, including the version after a supplied source subquotient |
| `Induction.BinaryProductConstituentExtraction` | Actual irreducible factor constituents from supplied finite-length derivatives |
| `CuspidalSupport.BinaryProductSupport` | Support addition from supplied supports and an actual irreducible product subquotient |

The inherited Leibniz proof uses the proved general two-orbit restriction
sequence and general left and right mixed derivative comparisons, then
exact image filtrations, reindexing and splicing. Its arbitrary-carrier
zero-rank branches use tensor/quotient maps. The exactness used for `Q`
is a proved composite of restriction, rank transport and normalized
mirabolic-minus functors. Those exactness proofs use general coinvariant
and compact-averaging arguments.

The factor extraction uses actual composition series, product
filtrations and the general simple-module extraction argument. Its
positive-rank quotient maps come from general smooth induction
surjectivity and the actual tensor image/kernel calculations. The
support-addition route uses the actual cuspidal-family concatenation
and its invariant-subspace quotient presentations. None of these
implemented routes uses a segment derivative identification or a
product-irreducibility conclusion.

The full recursive inventory at Library
`7a2e42fd31831029d34cafb155ffad911920df25` has 629 project modules,
including this entry, and 205 directly named external import roots.
All 628 inherited Lean/Markdown pairs are present, have nonempty
Markdown and are byte-identical to that published tree. There are no
missing project imports. The inventory
below lists project modules recursively and external roots directly;
it does not claim a separate recursive traversal of Mathlib.

Every inherited module is covered by the union of the three direct
inputs' earlier dependency inventories. The new entry is the only
module outside that union. The current Lean bodies agree with their
latest available input inventories except for the meaning-preserving
movement of elementary quotient declarations out of
`Analysis.Local.QuotientMeasure` and `QuotientTopology` into
`Group.LeftQuotient`. The moved core was read with its paired Markdown:
it contains the right-relation quotient, invariant-function descent,
right translations and elementary open-projection, Hausdorffness and
local-compactness lemmas from Mathlib. It has no representation or
integration imports. The induction definitions re-export the same core.
This introduces no new mathematical input to the routes above.
The remaining differences in the input inventories are completion of
their paired documentation.

Exactly 18 `Classification` modules occur:
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`,
`FiniteLengthStatement`, `RelativeGenericityStatement`,
`RelativeJacquetMultiplicityStatement`,
`RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
`SupercuspidalSupport`, `SupercuspidalTwist`, `Tempered`,
`TemperedInductionStatement`, and `TemperedSupportStatement`.
The new proof uses the actual support and subquotient definitions and
the proved general constructions just identified. The inherited broader
statement interfaces are not supplied as unproved theorem hypotheses.
In particular the finite length needed here is explicit for every
factor derivative.

The module uses proved general derivative infrastructure only, with the
exclusions of the table below. It proves no support-only
terminal-truncation segment bound and no strengthening of it.

| Excluded result or boundary | Check on the closure and implemented route |
| --- | --- |
| Ze80 §§3.5/9.6, their formulas and proofs | No segment derivative module is imported or invoked. The derivative inputs are proved general Leibniz and exactness constructions. |
| Full segment/head/socle Jacquet formulas and exponent norm formula, including `SegmentFullJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentHeadJacquetFormula` and `SegmentSpecialJacquetExponentNormFormula` | None supplies a proof dependency. General coinvariant exactness and induction maps do not apply those conclusions. |
| The special-head product criterion `SegmentHeadProductIrreducibility` in either direction and socle product criterion `SegmentSocleProductIrreducibility` | Neither conclusion, its proof nor a downstream consumer is imported or used. |
| `GenericSegmentProductUniqueness` | No generic unlinked-product uniqueness or comparison of different segment products is used. |
| Multisegment exhaustion, ordered strong-head existence, quotient coverage, ordered conversion | No such conclusion supplies an input; the indexing here is only feasible derivative orders. |
| Tempered uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable exhaustion, regular exhaustion | None of these conclusions or their proof routes is a dependency. |
| Segment-socle part of the derivative statements (`SegmentSocleDerivativesStatement`), linked-pair structure, adjacent commutation and two-supercuspidal product criteria | None is used. General product subquotients and filtration extraction assume no such criterion. |
| Whittaker irreducible/Levi/supercuspidal coinvariant finiteness and dependent mirabolic finite length | These conclusions are absent. Required derivative finite length is a stated hypothesis, and general minus exactness does not obtain it from these excluded routes. |
| Original datum universe and repeated supports | Actual carriers stay at `max uF uV`; supplied support witnesses stay at original `uV`; multiset addition retains every multiplicity. |
| Unpublished results | All imported inputs are published. No unpublished support bound or stronger derivative statement is used. |

A recursive lexical scan after removing nested comments and strings
found no audited excluded-name matches, proof holes,
new axioms or prohibited execution syntax. The explicit proof-route
checks above supplement that scan; a name scan alone would not establish
independence.

## Validation and remaining scope

A development check compiled
this module with zero errors and warnings. Exact inspection of `supportData`
reports a definition,
independent level parameters `uF,uV`, and only `propext`,
`Classical.choice` and `Quot.sound`. No Lean edit followed that
inspection.

This module supplies a binary aggregation step from explicit finite-length
and support hypotheses. It proves no unconditional support existence,
support uniqueness, equality with an independently specified support,
derivative irreducibility, identification with a truncated special head,
multiplicity formula or full derivative formula. The support-only
terminal-truncation bound, its dual initial bound, finite-product
iteration, support equality needed in the argument for
`SegmentHeadProductIrreducibility`, nonlinkage
survival and the linked converse are not proved here.
The full repeated-segment special-head product irreducibility criterion
is not proved by this module; it is proved by
`segmentHeadProductIrreducibility` in
`Classification.SegmentHeadProductIrreducibilityProof`.

## Complete import inventory

Each prefix below is followed by its immediate module suffixes; concatenating
them with a dot expands to the full import names.

### Project modules

- `Langlands.Algebra`: `CommutingDimensionHelpers`, `CommutingDimensionNilpotent`, `CommutingDimensionNumerics`, `CommutingDimensionPrimary`, `CommutingDimensionRecurrence`, `MultisetOfFn`, `SandwichDimensionBoundProof`, `SandwichDimensionBoundStatement`, `SeparatedMatrixRepresentations`.
- `Langlands.Analysis.Local`: `CompactOpenCoverUnimodularityProof`, `CompactOpenCoverUnimodularityStatement`, `ModularCompactAverage`, `QuotientAutomorphismProof`, `QuotientAutomorphismStatement`, `QuotientAverageReal`, `QuotientAveragingKernel`, `QuotientComplex`, `QuotientFunctional`, `QuotientMass`, `QuotientMeasure`, `QuotientMeasureExistence`, `QuotientMeasureExistenceStatement`, `QuotientMeasurePrerequisites`, `QuotientPositiveLifting`, `QuotientTopology`, `QuotientTranslation`, `SplitKernelQuotient`.
- `Langlands.Group`: `HaarModulus`, `LeftQuotient`.
- `Langlands.Group.GL`: `Basic`, `BlockContractionProof`, `BlockContractionStatement`, `BlockDeterminant`, `BlockIwahoriBasis`, `BlockIwahoriBasisStatement`, `BlockIwahoriDefinitions`, `BlockModulus`, `BlockUnipotent`, `Blocks`, `CartanProof`, `CartanStatement`, `CompactOpen`, `CountabilityProof`, `CountabilityStatement`, `DominantExponentGeneration`, `HeadTailBlocks`, `Maps`, `Mirabolic`, `MirabolicMixedOrbitCoverageProof`, `MirabolicMixedOrbitCoverageStatement`, `MirabolicMixedOrbitData`, `MirabolicMixedOrbitRadicals`, `MirabolicMixedOrbitSectionCoefficients`, `MirabolicMixedOrbitSections`, `MirabolicMixedOrbitSpecializations`, `MirabolicMixedOrbitStages`, `MirabolicMixedProductSubgroups`, `MirabolicModularCharacterProof`, `MirabolicModularCharacterStatement`, `MirabolicModulusProof`, `MirabolicModulusStatement`, `MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`, `OneBlockShape`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `PadicOppositeBlocks`, `PadicUpperUnipotent`, `PrincipalBlockFactorizationProof`, `PrincipalBlockFactorizationStatement`, `PrincipalLevelDominance`, `RankMaps`, `RankReindex`, `RefinementCoordinates`, `ReindexCongr`, `ReverseBlocks`, `SingleBlock`, `SingletonBlocks`, `TriangularParabolic`, `UnramifiedCharacter`, `UpperUnipotent`, `UpperUnipotentCompactContainmentProof`, `UpperUnipotentCompactContainmentStatement`.
- `Langlands.HarmonicAnalysis`: `AlgebraicIntegral`, `AlgebraicIntegrand`, `Basic`, `Conductor`, `HaarConjugacy`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`.
- `Langlands.LocalFactor.Euler`: `Definitions`.
- `Langlands.LocalFactor.Harmonic`: `Statement`.
- `Langlands.LocalField`: `Canonical`, `CanonicalProof`, `CanonicalStatement`, `Definitions`, `Topology`, `Uniformizer`.
- `Langlands.LocalField.Normalization`: `Definitions`, `Proof`, `Statement`.
- `Langlands.Representation`: `OrbitSpan`, `SubrepresentationLattice`.
- `Langlands.Representation.Category`: `Abelian`, `Basic`, `ClassInvariants`, `Subquotients`, `Twist`.
- `Langlands.Representation.Classification`: `CanonicalConstituents`, `ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`, `FiniteLengthStatement`, `RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`, `RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, `SupercuspidalSupport`, `SupercuspidalTwist`, `Tempered`, `TemperedInductionStatement`, `TemperedSupportStatement`.
- `Langlands.Representation.Compact`: `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.CompactCoefficient`: `AdmissibleComplement`, `AdmissibleLifting`, `AdmissibleRetraction`, `AmbientProjector`, `Classes`, `ConditionalProjection`, `FixedLevelFiniteness`, `FixedVectorsFiniteDimensional`, `GroupTransport`, `Isotypic`, `IsotypicTransport`, `NormalSubgroupDecomposition`, `OrthogonalProjectorFamily`, `SemisimplicityProof`, `SemisimplicityStatement`, `TotalCompactness`, `TotalProjector`.
- `Langlands.Representation.Conductor`: `Congruence`, `Definitions`, `PrincipalCongruence`, `PrincipalCongruenceBasisProof`, `PrincipalCongruenceBasisStatement`.
- `Langlands.Representation.CuspidalSupport`: `AllRankBinaryCuspidalConcatenation`, `AssociatedGeometricPiecesEquivalenceProof`, `AssociatedGeometricPiecesStatement`, `AssociationForwardStatement`, `AssociationLawsProof`, `AssociationLawsStatement`, `AssociationReduction`, `BinaryCuspidalConcatenation`, `BinaryProductSupport`, `BlockMap`, `BlockPermutation`, `CompactCoefficientFinitenessProof`, `CompactCoefficientFinitenessReduction`, `CompactCoefficientFinitenessStatement`, `CuspidalTensorAssociationProof`, `CuspidalTensorStatement`, `DeterminantUnit`, `DeterminantUnitCartanSupport`, `DeterminantUnitCentralCompactnessProof`, `DeterminantUnitCentralCompactnessStatement`, `DeterminantUnitCornerStructureProof`, `DeterminantUnitCornerStructureStatement`, `DeterminantUnitStructureProof`, `DeterminantUnitStructureStatement`, `DualAveraging`, `FiniteBlockShapes`, `GroupTransport`, `HarishChandraAssembly`, `HarishChandraBoundaryProof`, `HarishChandraBoundaryStatement`, `HarishChandraConverseProof`, `HarishChandraConverseStatement`, `HarishChandraForwardProof`, `HarishChandraStatement`, `InducedJacquetCount`, `JacquetDetectingFamilyLengthProof`, `JacquetDetectingFamilyLengthStatement`, `JacquetInductionStatement`, `JacquetLengthDetector`, `JacquetSubquotientProof`, `JacquetSubquotientStatement`, `JacquetVanishingSubgroups`, `LeviAdmissibleFactorizationProof`, `LeviAdmissibleFactorizationStatement`, `LeviAssociation`, `LeviCompactPart`, `LeviDecompositionAssembly`, `LeviDefinitions`, `LeviGapVanishing`, `LeviQuasicuspidalDecompositionProof`, `LeviSplitContraction`, `MinimalConjugatingCosetsProof`, `MinimalJacquetProof`, `MinimalJacquetStatement`, `NaturalProjectorDecomposition`, `NormalizedCuspidalInductionStatement`, `PointwiseProjectorSum`, `QuasicuspidalEmbeddingProof`, `QuasicuspidalFiniteLengthProof`, `QuasicuspidalFiniteLengthStatement`, `QuasicuspidalPrerequisitesStatement`, `QuasicuspidalStructureStatement`, `RefinedJacquetLengthProof`, `RefinedJacquetLengthStatement`, `TotalConjugatingCountProof`, `TotalConjugatingCountStatement`.
- `Langlands.Representation.Derivative`: `BinaryDerivativeSupportAggregation`, `GeneralLinearDerivativeExactnessProof`, `GeneralLinearDerivativeExactnessStatement`, `GeneralLinearDerivativeLeibnizBoundary`, `GeneralLinearDerivativeLeibnizFiltrationProof`, `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeftMixedProductDerivativeProof`, `LeftMixedProductHigher`, `LeftMixedProductVanishing`, `LeftMixedProductZeroRank`, `LeibnizConstituentExtraction`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizPositiveGluing`, `LeibnizQuotientPiece`, `LeibnizRankZeroBoundary`, `LeibnizRankZeroGluing`, `LeibnizRestrictionCompat`, `LeibnizRestrictionExact`, `LeibnizZeroFirstPiece`, `LevelCalculus`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionProof`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicDeterminant`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusExactnessProof`, `MirabolicMinusExactnessStatement`, `MirabolicMixedOrbitCharacters`, `MirabolicPhiMinusMackey`, `MirabolicPlus`, `MirabolicProductMinusBoundary`, `MirabolicProductMinusCompatibilityStatement`, `MirabolicProductMinusLeftPhi`, `MirabolicProductMinusLeftPhiCoefficient`, `MirabolicProductMinusLeftPhiCompactComparison`, `MirabolicProductMinusLeftPhiHaar`, `MirabolicProductMinusLeftPhiHostTransport`, `MirabolicProductMinusLeftPhiIdentityComparison`, `MirabolicProductMinusLeftPhiInductionNormalization`, `MirabolicProductMinusLeftPhiLocalization`, `MirabolicProductMinusLeftPhiMackeyLocalization`, `MirabolicProductMinusLeftPhiNormalization`, `MirabolicProductMinusLeftPhiNormalizedSection`, `MirabolicProductMinusLeftPhiSection`, `MirabolicProductMinusLeftPhiSourceAction`, `MirabolicProductMinusLeftPhiSourceComparison`, `MirabolicProductMinusLeftPhiStagesComparison`, `MirabolicProductMinusLeftPsi`, `MirabolicProductMinusLeftPsiInduction`, `MirabolicProductMinusPhiKernelComparison`, `MirabolicProductMinusRightBoundary`, `MirabolicProductMinusRightPhi`, `MirabolicProductMinusRightPhiAssembly`, `MirabolicProductMinusRightPhiCycle`, `MirabolicProductMinusRightPhiCycleCoefficient`, `MirabolicProductMinusRightPhiCycleGroups`, `MirabolicProductMinusRightPhiIdentity`, `MirabolicProductMinusRightPhiIdentityCoefficient`, `MirabolicProductMinusRightPhiIdentityGroups`, `MirabolicProductMinusRightPsi`, `MirabolicProductMinusRightPsiCoefficient`, `MirabolicProductMinusRightPsiGroups`, `MirabolicProductMinusRightPsiZero`, `MirabolicProductRestriction`, `MirabolicProductRestrictionCasts`, `MirabolicProductRestrictionFactors`, `MirabolicProductRestrictionMackey`, `MirabolicProductRestrictionOrbits`, `MirabolicProductRestrictionStabilizers`, `MirabolicProductRestrictionStatement`, `MirabolicProductRestrictionTransport`, `MixedProductDerivativeStatement`, `MixedProductRankCast`, `OrderRecursion`, `ProductVanishing`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationProof`, `RightMixedProductDerivativeFiltrationStatement`, `RightMixedProductDerivativePositive`, `RightMixedProductZeroRank`, `ShortExactFunctorLaws`, `ZeroRankTensor`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Exponents`: `Central`, `ComplexTwistFamilies`, `DualJacquet`, `DualJacquetStatement`, `Jacquet`, `NilpotenceIndex`, `ParabolicPair`, `RealTwistFamilies`, `SupportedRegularMultiplicityBranchObstructionStatement`, `WeylBranchPiecesStatement`, `WeylBranchPiecesSubquotient`.
- `Langlands.Representation.Filtration`: `ActualGradedExtraction`, `CoarseJacquetExtraction`, `CoarseJacquetFactorization`, `Definitions`, `ExactConstituentExtraction`, `ExactSmoothSubquotients`, `ExactSmoothTransport`, `GluedFamily`, `GradedRefinementProof`, `GradedRefinementStatement`, `IntervalLiftProof`, `IntervalLiftStatement`, `IrreducibleEmbedding`, `IsoTransport`, `JordanHolderStatement`, `JordanHolderTransportProof`, `LengthCriterionProof`, `LengthCriterionStatement`, `LengthTwoMatching`, `LengthTwoMatchingStatement`, `MultiplicityStatement`, `ObjectDefinitions`, `ObjectTransport`, `OneStep`, `Precomposition`, `QuotientFirstIso`, `QuotientTail`, `RepresentationLength`, `SmoothGradedObject`, `Splicing`, `SubquotientAlgebraProof`, `SubquotientAlgebraStatement`, `SubsingletonProof`, `Transport`, `VanishingStatement`.
- `Langlands.Representation.Filtration.Splicing`: `Basic`.
- `Langlands.Representation.Geometric`: `ClosedSubgroupAssembly`, `ClosedSubgroupDefinitions`, `ClosedSubgroupMackeyProof`, `ClosedSubgroupStatement`, `CompactOrbitRestriction`, `CosetAction`, `CosetOrbitHomeomorph`, `FlattenedLevi`, `GeometricLemmaStatement`, `IntersectionTransport`, `OrbitRestriction`, `OrbitSectionExtensionProof`, `OrbitSectionExtensionStatement`, `RefinementDefinitions`, `RefinementFunctors`, `WeylDefinitions`, `WeylMinimalRepresentativeProof`, `WeylStatement`, `WeylUniquenessProof`, `WeylUniquenessStatement`.
- `Langlands.Representation.Hecke`: `ActionIntegrand`, `ActionProjection`, `CommonInvarianceProof`, `CommonInvarianceStatement`, `Convolution`, `Corner`, `CornerAction`, `DoubleCoset`, `DoubleCosetSandwich`, `IntegratedAction`, `IntegratedConvolution`, `NormalizedIndicator`, `TestFunction`.
- `Langlands.Representation.Induction`: `BinaryPositiveCompact`, `BinaryProduct`, `BinaryProductConstituentExtraction`, `BinaryProductSubquotients`, `BlockFactors`, `CharacterTwistProof`, `CompactAutomorphism`, `CompactAutomorphismIntegralProof`, `CompactAutomorphismIntegralStatement`, `CompactCoinvariantBijectivityProof`, `CompactCoinvariantBijectivityStatement`, `CompactCoinvariantIntegral`, `CompactCoinvariantLocalInverseProof`, `CompactCoinvariantLocalInverseStatement`, `CompactLocalSection`, `CompactLocalSectionSpanningProof`, `CompactLocalSectionSpanningStatement`, `CompactLocallyConstant`, `CompactQuotientCutoff`, `CompactQuotientProof`, `CompactSurjectivityProof`, `CompactSurjectivityStatement`, `CompactTransitivityProof`, `CompactTransitivityStatement`, `ConjugateParabolic`, `Definitions`, `EmptyProductUnit`, `Equivalences`, `FiniteProductTensor`, `FiniteProductTensorBijectiveProof`, `FiniteProductTensorBijectiveStatement`, `InverseTranspose`, `NormalCoinvariantKernelProof`, `NormalCoinvariantKernelStatement`, `NormalCoinvariantMap`, `NormalCoinvariantProof`, `NormalCoinvariantStatement`, `NormalSplitComparison`, `OppositeParabolic`, `Parabolic`, `SingleBlock`, `SplitKernelCharacter`, `SplitKernelCharacterExtension`, `SplitKernelCompact`, `SplitKernelCovariance`, `SplitKernelEquivariant`, `SplitKernelHaarTrivial`, `SplitKernelIntegral`, `SplitKernelLocalizationData`, `SplitKernelSectionAction`, `SplitQuotientProof`, `SplitQuotientStatement`, `SplitStagesCharacterComparison`, `SplitStagesCharacterComparisonStatement`, `SplitStagesCharacterIntegrand`, `SplitStagesComparison`, `SplitStagesRetraction`, `StructuralStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.Jacquet`: `BlockCompressionProof`, `BlockCompressionStatement`, `BlockPowerKernelProof`, `CanonicalLiftBijectivityProof`, `CanonicalLiftDefinitions`, `CanonicalLiftStatement`, `CharacterAveraging`, `CharacterTwistEquiv`, `Coinvariants`, `CompressionStabilizationProof`, `CompressionStabilizationStatement`, `ExactProof`, `ExactStatement`, `Localization`, `LocalizationExactnessProof`, `LocalizationExactnessStatement`, `LocalizationTransport`, `Normalized`, `Parabolic`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`, `ModuloCenter`.
- `Langlands.Representation.Mirabolic`: `LeftMixedProductSuccessor`, `MixedProducts`.
- `Langlands.Representation.Parabolic`: `ComposedFunctors`, `FlattenedJacquetComparisonProof`, `FlattenedJacquetComparisonStatement`, `FlattenedJacquetQuotientProof`, `FlattenedJacquetQuotientStatement`, `FlattenedProductInduction`, `FlattenedRefinementModulusCalculation`, `FlattenedTensorOccurrences`, `GeometricPrerequisitesStatement`, `InducedMapSurjectivity`, `InductionFactorMatchingProof`, `InductionFactorMatchingStatement`, `InductionFiltration`, `InductionSubrepresentation`, `JacquetFiniteGenerationProof`, `JacquetFiniteGenerationStatement`, `LeviBridges`, `NormalizedJacquetAdmissibilityProof`, `NormalizedJacquetExactnessProof`, `NormalizedJacquetStatement`, `OppositeJacquetMap`, `OppositeRefinementDefinitions`, `OppositeRefinementFunctors`, `OrderedRefinementInduction`, `OrderedRefinementTensorInduction`, `ProductInductionFiltration`, `ProductInductionSubrepresentation`, `QuotientCompactProof`, `RefinedInductionTensorMap`, `RefinedInductionTensorNormalization`, `RefinedInductionTensorProof`, `RefinedInductionTensorStatement`, `RefinedJacquetTensor`, `RefinedOppositeJacquetTensor`, `RefinedTensorOccurrences`, `RefinementCharacter`, `RefinementComposition`, `RefinementCoordinatesNormalizationProof`, `RefinementCoordinatesNormalizationStatement`, `RefinementInductionTransitivityProof`, `RefinementJacquetTransitivityProof`, `RefinementPreimage`, `RefinementTransitivityStatement`, `UnipotentFiniteContainment`.
- `Langlands.Representation.RankinSelberg`: `GeneralLinearUnimodularity`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `Measures`, `QuotientIntegrals`, `UnimodularityStatement`, `UnipotentUnimodularity`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`.
- `Langlands.Representation.Shahidi`: `Geometry`, `Induction`, `TwoBlocks`.
- `Langlands.Representation.Smooth`: `Definitions`, `SmallRealizationProof`, `SmallRealizationStatement`.
- `Langlands.Representation.Smooth.Admissibility`: `CofinalProof`, `CofinalStatement`, `EmbeddingProof`, `EmbeddingStatement`, `EquivalenceProof`, `EquivalenceStatement`, `ExactProof`, `ExactStatement`.
- `Langlands.Representation.Smooth.Contragredient`: `AdmissibleDualityProof`, `AdmissibleDualityStatement`, `CompactDualityProof`, `CompactDualityStatement`, `Definitions`, `ExactProof`, `ExactStatement`, `FixedVectorsDefinitions`, `HomDualityProof`, `HomDualityStatement`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Smooth.Factorization`: `MultiplicityDefinitions`, `TwoFactorExistenceProof`, `TwoFactorStatement`.
- `Langlands.Representation.Smooth.FixedVectors`: `Definitions`, `FiniteTypes`, `FiniteTypesStatement`, `LawsProof`, `LawsStatement`, `OrderProof`, `OrderStatement`.
- `Langlands.Representation.Smooth.Schur`: `Proof`, `Statement`.
- `Langlands.Representation.Smooth.SmoothPart`: `BasicProof`, `BasicStatement`, `Definitions`, `FixedVectorsDefinitions`.
- `Langlands.Representation.Smooth.Transfer`: `GroupEquivalence`, `PullbackProof`, `PullbackStatement`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Tensor`: `CharacterLocalization`, `ExternalFiltration`, `ExternalMapSurjectivityProof`, `ExternalMapSurjectivityStatement`, `ExternalSubquotient`, `ExternalSubrepresentation`, `Filtration`, `Finite`, `FiniteEquivalences`, `FiniteFiltration`, `FiniteProperties`, `FiniteRegrouping`, `FlattenedGLRefinement`, `GLRefinement`, `OneFactor`, `SmoothSubquotients`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `LeviComplexPower`, `LeviRealPower`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Unitary`: `Basic`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`, `Iwasawa`.
- `Langlands.Topology`: `CompactNormCharacter`.
- `Langlands.Topology.CompactOpen`: `ConjugationStabilizer`, `NeighborhoodBasis`, `NeighborhoodBasisStatement`.
- `Langlands.Topology.Nonarchimedean`: `Subgroup`.
- `Langlands.Weil.Representation`: `Basic`, `Determinant`, `IsomorphismInvarianceProof`, `Operations`.

### External import roots

- `Lean.Elab.Tactic`: `Omega`.
- `Mathlib`: `Tactic`.
- `Mathlib.Algebra.Algebra`: `NonUnitalHom`, `NonUnitalSubalgebra`.
- `Mathlib.Algebra.Algebra.Subalgebra`: `Lattice`.
- `Mathlib.Algebra.BigOperators`: `Fin`, `Finprod`, `Pi`.
- `Mathlib.Algebra.BigOperators.Group.Finset`: `Basic`.
- `Mathlib.Algebra.BigOperators.Group.Multiset`: `Basic`.
- `Mathlib.Algebra.Category.ModuleCat`: `Basic`.
- `Mathlib.Algebra.CharP`: `Basic`.
- `Mathlib.Algebra.Exact`: `Basic`.
- `Mathlib.Algebra.Group.Equiv`: `TypeTags`.
- `Mathlib.Algebra.Group.Hom`: `Instances`.
- `Mathlib.Algebra.Group.Subgroup`: `Ker`.
- `Mathlib.Algebra.Group.Submonoid`: `Basic`.
- `Mathlib.Algebra.Module`: `ULift`.
- `Mathlib.Algebra.Module.Submodule`: `Map`.
- `Mathlib.Algebra.Order.Archimedean`: `Basic`.
- `Mathlib.Algebra.Order.BigOperators.Group`: `Finset`.
- `Mathlib.Algebra.Polynomial`: `Lifts`.
- `Mathlib.Algebra.Ring`: `GeomSum`.
- `Mathlib.Analysis`: `MeanInequalitiesPow`.
- `Mathlib.Analysis.Complex`: `Basic`, `Circle`.
- `Mathlib.Analysis.Complex.Polynomial`: `Basic`.
- `Mathlib.Analysis.Fourier`: `FourierTransform`.
- `Mathlib.Analysis.InnerProductSpace`: `Defs`.
- `Mathlib.Analysis.Matrix`: `MeasurableSpace`, `Normed`.
- `Mathlib.Analysis.Normed.Module`: `FiniteDimension`.
- `Mathlib.Analysis.Normed.Unbundled`: `SpectralNorm`.
- `Mathlib.Analysis.Real`: `Sqrt`.
- `Mathlib.Analysis.SpecialFunctions.Complex`: `Circle`.
- `Mathlib.Analysis.SpecialFunctions.Pow`: `Complex`, `NNReal`, `Real`.
- `Mathlib.Basic.Complex`: `Basic`.
- `Mathlib.CategoryTheory`: `Skeletal`.
- `Mathlib.CategoryTheory.Abelian`: `Subcategory`.
- `Mathlib.CategoryTheory.Discrete`: `Basic`.
- `Mathlib.CategoryTheory.Limits.ConcreteCategory`: `Basic`.
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes`: `Zero`.
- `Mathlib.CategoryTheory.ObjectProperty`: `FullSubcategory`.
- `Mathlib.CategoryTheory.Pi`: `Basic`.
- `Mathlib.CategoryTheory.Products`: `Basic`.
- `Mathlib.Combinatorics.Enumerative`: `Composition`.
- `Mathlib.Data.ENat`: `Basic`, `BigOperators`.
- `Mathlib.Data.Fin`: `Rev`.
- `Mathlib.Data.Fin.Tuple`: `Basic`, `Sort`.
- `Mathlib.Data.Finset`: `NatAntidiagonal`.
- `Mathlib.Data.Fintype`: `EquivFin`, `Sum`.
- `Mathlib.Data.Int`: `Interval`, `LeastGreatest`.
- `Mathlib.Data.Matrix`: `Basic`, `Block`.
- `Mathlib.Data.Nat`: `Find`.
- `Mathlib.Data.Set.Finite`: `Basic`.
- `Mathlib.Data.ZMod`: `Basic`.
- `Mathlib.FieldTheory.Finite`: `Basic`.
- `Mathlib.FieldTheory.RatFunc`: `AsPolynomial`.
- `Mathlib.GroupTheory`: `DoubleCoset`, `Index`.
- `Mathlib.GroupTheory.Coset`: `Defs`.
- `Mathlib.GroupTheory.GroupAction`: `ConjAct`, `Quotient`.
- `Mathlib.GroupTheory.QuotientGroup`: `Defs`.
- `Mathlib.GroupTheory.Subgroup`: `Centralizer`.
- `Mathlib.LinearAlgebra`: `Determinant`, `Isomorphisms`, `Projection`.
- `Mathlib.LinearAlgebra.AffineSpace`: `AffineMap`.
- `Mathlib.LinearAlgebra.Basis`: `VectorSpace`.
- `Mathlib.LinearAlgebra.Charpoly`: `Basic`, `ToMatrix`.
- `Mathlib.LinearAlgebra.Dimension`: `Constructions`.
- `Mathlib.LinearAlgebra.Dual`: `Lemmas`.
- `Mathlib.LinearAlgebra.Eigenspace`: `Basic`, `Pi`, `Triangularizable`.
- `Mathlib.LinearAlgebra.FiniteDimensional`: `Basic`, `Defs`.
- `Mathlib.LinearAlgebra.FreeModule.Finite`: `Matrix`.
- `Mathlib.LinearAlgebra.Matrix`: `Block`, `Diagonal`, `Kronecker`, `Permutation`, `Reindex`, `SchurComplement`, `Transvection`.
- `Mathlib.LinearAlgebra.Matrix.Charpoly`: `Coeff`.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup`: `Basic`, `Defs`.
- `Mathlib.LinearAlgebra.PiTensorProduct`: `Basic`, `Basis`, `Finite`, `Generators`.
- `Mathlib.LinearAlgebra.TensorProduct`: `Basis`, `Finiteness`, `RightExactness`.
- `Mathlib.Logic.Equiv.Fin`: `Basic`.
- `Mathlib.MeasureTheory.Constructions`: `Pi`.
- `Mathlib.MeasureTheory.Function`: `LocallyIntegrable`, `SimpleFunc`.
- `Mathlib.MeasureTheory.Function.LpSeminorm`: `Defs`.
- `Mathlib.MeasureTheory.Group`: `Integral`, `LIntegral`, `Measure`, `ModularCharacter`.
- `Mathlib.MeasureTheory.Integral`: `Marginal`, `Prod`.
- `Mathlib.MeasureTheory.Integral.Bochner`: `Basic`, `ContinuousLinearMap`, `Set`.
- `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani`: `Real`.
- `Mathlib.MeasureTheory.Measure`: `Regular`.
- `Mathlib.MeasureTheory.Measure.Haar`: `Basic`, `DistribChar`, `MulEquivHaarChar`, `Unique`.
- `Mathlib.MeasureTheory.Measure.Lebesgue`: `Basic`.
- `Mathlib.MeasureTheory.Measure.Typeclasses`: `Finite`.
- `Mathlib.NumberTheory.LocalField`: `Basic`.
- `Mathlib.NumberTheory.Padics`: `LocalField`, `RingHoms`.
- `Mathlib.Order`: `Atoms`, `WithBot`.
- `Mathlib.Order.Hom`: `Set`.
- `Mathlib.Order.Interval.Finset`: `Fin`.
- `Mathlib.RepresentationTheory`: `Basic`, `Coinduced`, `Coinvariants`, `Equiv`, `Intertwining`, `Invariants`, `Irreducible`, `Semisimple`, `Subrepresentation`.
- `Mathlib.RepresentationTheory.Rep`: `Basic`, `Res`.
- `Mathlib.RingTheory`: `FiniteLength`, `Length`, `Nakayama`, `PowerBasis`, `PrincipalIdealDomain`.
- `Mathlib.RingTheory.Adjoin`: `Basic`.
- `Mathlib.RingTheory.Adjoin.Polynomial`: `Basic`.
- `Mathlib.RingTheory.Artinian`: `Module`.
- `Mathlib.RingTheory.DedekindDomain`: `IntegralClosure`.
- `Mathlib.RingTheory.Finiteness`: `Basic`, `Defs`, `Finsupp`.
- `Mathlib.RingTheory.Flat`: `Basic`.
- `Mathlib.RingTheory.Ideal.Quotient`: `Operations`.
- `Mathlib.RingTheory.Noetherian`: `Basic`, `Defs`.
- `Mathlib.RingTheory.Polynomial`: `Basic`.
- `Mathlib.RingTheory.RamificationInertia`: `Basic`.
- `Mathlib.RingTheory.SimpleModule`: `Basic`.
- `Mathlib.RingTheory.Valuation`: `Integral`.
- `Mathlib.Tactic`: `Group`, `Linarith`, `NoncommRing`.
- `Mathlib.Topology`: `Bases`, `LocallyClosed`, `UrysohnsLemma`.
- `Mathlib.Topology.Algebra`: `ContinuousMonoidHom`, `MulAction`, `OpenSubgroup`, `Support`.
- `Mathlib.Topology.Algebra.Group`: `Basic`, `Matrix`, `Neighborhood`, `OpenMapping`, `Pointwise`, `Quotient`, `Subgroup`, `Units`.
- `Mathlib.Topology.Algebra.Module`: `FiniteDimension`, `ModuleTopology`.
- `Mathlib.Topology.Algebra.Nonarchimedean`: `Basic`, `TotallyDisconnected`.
- `Mathlib.Topology.Algebra.ProperAction`: `Basic`.
- `Mathlib.Topology.Algebra.Ring`: `Compact`.
- `Mathlib.Topology.Algebra.ValuativeRel`: `ValuativeTopology`.
- `Mathlib.Topology.Algebra.Valued`: `NormedValued`.
- `Mathlib.Topology.Baire`: `LocallyCompactRegular`.
- `Mathlib.Topology.Compactness`: `Compact`, `LocallyCompact`, `SigmaCompact`.
- `Mathlib.Topology.Connected`: `TotallyDisconnected`.
- `Mathlib.Topology.ContinuousMap`: `CompactlySupported`.
- `Mathlib.Topology.Homeomorph`: `Lemmas`, `Quotient`.
- `Mathlib.Topology.Instances`: `Matrix`.
- `Mathlib.Topology.Instances.NNReal`: `Lemmas`.
- `Mathlib.Topology.Instances.Real`: `Lemmas`.
- `Mathlib.Topology.LocallyConstant`: `Algebra`, `Basic`.
- `Mathlib.Topology.Order`: `Compact`.
- `Mathlib.Topology.Separation`: `Profinite`.
