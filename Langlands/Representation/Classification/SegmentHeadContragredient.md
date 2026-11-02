# Endpoint reversal and smooth duality of individual special heads

Author: Worker 357.

This internal construction defines endpoint reversal for one segment and proves
smooth duality of every supplied individual special head. It is a focused
prerequisite of task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`. The full product
irreducibility criterion remains a separate, unproved obligation.

## Parameters and conclusions

The segment results range over an arbitrary prime `p`, actual
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and independent
universes `uF` and `uV`. A segment has its original cuspidal datum in universe
`uV`. Each supplied segment quotient or head has actual smooth complex carrier
in `Type (max uF uV)`, matching the existing segment induction. All topologies
and topological group structures are those supplied by `T`.

Write `D` for `CuspidalProductContragredient.dualDatum`, the published smooth
contragredient on cuspidal data. For a segment `Delta` of length `m`, define
`Delta.dual` by base `D Delta.last` and unchanged length. This is the segment
whose ordered members are

`D Delta.last, D (Delta.member (m-2)), ..., D Delta.base`.

The paired Lean proves:

- `Segment.dual_length`, `dual_rank`, and `dual_degree`: length, positive
  cuspidal rank and total degree are unchanged.
- `Segment.dual_member`: for `i < m`, member `i` of the dual segment is
  `D (Delta.member (m-1-i))`.
- `Segment.dual_last` and `dual_dual`: its last member is `D Delta.base`, and
  duality is involutive.
- `Segment.dual_support`: the support set of the dual segment is the image
  of the original support set under `D`. This is a set statement about the
  existing segment support definition.
- `nonempty_contragredient_segmentInducedIso`: for an actual admissible
  smooth base `A` of positive rank `r`, and every natural length `m`, the
  smooth contragredient of its increasing induction is isomorphic to the
  decreasing induction of `|det|^(-(m-1)) A.contragredient`. Here `m-1` is
  natural subtraction followed by the real coercion. This induction lemma
  also permits `m=0`; its factor family is then empty. Its base carrier may
  be in any independent universe `uV`, while induction saturates to
  `max uF uV`.
- `IsSegmentQuotient.contragredient`: for any supplied irreducible quotient
  `pi` of an increasing segment induction, its actual smooth contragredient
  is a strong special head for `Delta.dual`.
- `IsSegmentHead.contragredient`: in particular, the same conclusion holds
  for every supplied strong special head.

The shared generic lemma `IsIrreducibleHead.of_targetEquiv`, imported from
[HeadTargetTransport](HeadTargetTransport.md), transports
a strong head along an equivalence of its target, preserving the equality of
all irreducible quotient kernels. It works for an arbitrary group and complex
representations in one carrier universe. `IsSegmentHead.of_equiv` applies this
transport with the same segment representative.

## Implemented proof

The segment arithmetic uses the published identities
`dualDatum_twist`, `dualDatum_dualDatum` and `CuspidalDatum.twist_twist`.
The finite reversal `i -> m-1-i` gives the member formula and the support
image formula. Positive length makes the reversal well defined and proves
involution. Rank and degree preservation are definitional.

For the induction isomorphism, set `B = BlockShape.uniform m r hr`. The
published `nonempty_contragredient_productEquiv` commutes smooth duality
with the normalized block product, keeping the same upper parabolic and
block order. Each factor of the increasing induction is admissible because
`A` is admissible and twisting by an open-kernel determinant character
preserves admissibility.

At block `i`, `smoothContragredientTwistEquiv` identifies the smooth dual
of `|det|^i A` with `|det|^(-i) A.contragredient`. The character equality

`|det|^(m-1-i) * |det|^(-(m-1)) = |det|^(-i)`

identifies this with factor `i` of the decreasing induction based at
`|det|^(-(m-1)) A.contragredient`. The proof uses the determinant-character
addition and inverse laws and the actual twist composition equality.
`Pi.isoMk` assembles the factor isomorphisms, and
`normalizedProductInductionFunctor.mapIso` transports them to the actual
induced objects. No permutation equivalence is used.

For a supplied irreducible segment quotient, unpack an actual supercuspidal
representative `A`, its datum equality, and an actual surjective intertwiner
`q : segmentInduced A -> pi`. The representative
`Av = twistedDualRep T (-(m-1)) A` realizes the base of `Delta.dual`:
contragredience negates the last member's twist. The proof checks this
identity on the supercuspidal class fields to keep the rank indices fixed.

The published general `CuspidalSupport.cuspidalEmbedding` proves that the
irreducible `pi` is admissible. The published smooth-dual irreducibility
theorem then proves that `pi.contragredient` is irreducible. Dualizing the
actual surjection `q` gives an injective intertwiner from
`pi.contragredient` to `(segmentInduced A).contragredient`;
`contragredientMap_injective_of_surjective` supplies injectivity. Compose
with the induction isomorphism just constructed to inject this same
representation into `segmentInducedDown Av`.

The independently published `segmentSpecialConstituentExistence` supplies
an actual strong special head `pi0` for the dual segment.
`IsSegmentHead.nonempty_equiv_of_down_subrepresentation` identifies our
irreducible injected representation with `pi0`, using the independently
published characterization of each supplied individual head as the strong
socle of decreasing induction. Transport the full strong head relation
along the inverse equivalence. The transport composes the quotient with
the equivalence and uses its injectivity to preserve every quotient
kernel. Finally, a strong segment head is an irreducible segment quotient,
so the head corollary is immediate.

The claim about any irreducible segment quotient is derived from the same
actual injection and decreasing strong socle; it assumes no uniqueness or
classification result for arbitrary products.

## Published inputs and provenance

This is an internal deduction, with no new literature assertion as a premise.
The substantial direct modules are:

- `Classification.CuspidalProductContragredient`, for cuspidal dual data,
  twist compatibility, actual twisted-dual representatives and normalized
  product duality. Its general product-duality proof uses the proved
  admissible normalized-induction duality and the proved smooth-dual tensor
  bijection; its datum duality uses the proved supercuspidal dual closure.
- `Classification.SegmentHeadDecreasingSocle`, for target-independent
  characterization of every supplied special head as the strong socle of
  each decreasing representative. Its proof compares the published
  individual-head existence result with actual canonical heads and socles.

Both direct pairs were freshly checked against accepted, published records.
The former was independently approved by Reviewer 6069 and published at
Library `9a8ca758097242bde4147f33304f43fceef22fa4`; the latter was independently
approved by Reviewer 6998 and published at Library
`31d47a6f0dabd6dff6c65e1b78f4821ddedc9bc8`. Their frozen pair hashes still
match the current Library exactly. The full independent acceptance reports
were read. The present module uses no unaccepted draft or pending candidate.

Other proof inputs reached through these modules include
`Twist.SmoothPartDefinitions`, general contragredient injectivity and
irreducibility, `CuspidalSupport.CuspidalEmbeddingProof`, and
`Classification.SegmentSpecialConstituentExistenceProof`. The general
cuspidal embedding proof uses minimal-Jacquet/quasicuspidal induction,
admissibility of its inducing Levi representation, admissibility of
normalized induction and preservation under embeddings, with a separate
rank-zero proof. It supplies admissibility here without any multisegment
classification. The individual-head existence proof uses the actual
common-image multiplicity-one criterion, finite cuspidal Jacquet counts,
quotient/subobject detection, associated-induction maps, and segment
induction admissibility. Its head is that of increasing induction and its
socle is that of decreasing induction throughout.

## Independence audit

The recursive import inventory was computed at Library
`4bc52682538fe26ca525e0457642a4f58424e9b7`. It contains 666 project modules,
including this new entry, and 226 external import roots. Every one of the
665 inherited project Lean/Markdown pairs is present and byte-identical
to this published Library. All modules have nonempty paired Markdown.
The complete project and external inventories appear below. The inherited
proof routes were checked in addition to scanning names; an import-name
scan alone would not establish independence.

The union adds thirteen published modules to the decreasing-socle input's
652-module closure, plus this new entry: cuspidal product contragredience,
supercuspidal duality and its proof, cuspidal embedding and its rank-zero
case, block-character absorption and block equivalence, flattened refinement
modulus calculation, and the smooth-dual tensor definitions, injectivity
and surjectivity pairs. Those added routes are general smooth duality,
admissibility, tensor and induction constructions. There is no derivative
or mirabolic module in the union.

The permitted individual-head construction supplies only the individual
head and its decreasing strong socle used above. Its lower Jacquet
multiplicity computations and detectors are distinct from the excluded
full segment Jacquet equivalence. The inherited `Essential`, `Tempered`,
opposite-support adapters, `TemperedSupportStatement` and
`TemperedInductionStatement` provide definitions and general infrastructure;
no excluded analytic classification conclusion is assumed or proved here.

In particular, neither the import closure nor this proof uses the host
criterion, generic segment product uniqueness, multisegment exhaustion,
ordered strong-head existence, quotient coverage, ordered conversion,
tempered block uniqueness, square-integrable classification or exhaustion,
or regular exhaustion. Their host contract task identifiers are
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`,
`30341ae4-65f2-4a0e-9283-763db01a409e`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`8252833d-c269-41a9-824c-5879e531b23b`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, and
`bf433f0a-921a-428c-b0c0-6475438125ac`.

The host's additional exclusions, including the segment conclusions associated
with task prefixes `ed48ae06`, `b95105c6`, `55ad1e10`, `92aea10f`,
`2ae5cbe5`, and the segment-socle part of `8e5b4563`, remain excluded.
There is no use of Zelevinsky 1980 sections 3.5 or 9.6, their proof successors,
segment derivative formulas, segment-socle existence, full segment Jacquet
formulas, linked segment product structure or a segment product criterion.
This audit preserves the operator decisions
`bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920`, and
`30144f6f9b59540b88b6d4c1517892d9`, read in full. The latter's support-only
permission is not needed as an input here: the module asserts no derivative
support bound, derivative irreducibility, truncated-head identification,
multiplicity formula or complete derivative formula.

This contribution provides individual smooth duality. Product derivative
support aggregation, survival under nonlinkage, the linked converse, and the
full unchanged product irreducibility target remain separate obligations.

## Complete recursive project inventory

Within each block below, append each listed suffix to the stated prefix.
The inventory includes this entry. These are module names, not assumptions
that the theorems of every imported module are used in the proof.

Prefix `Langlands.Analysis.Local.`:

```text
CompactOpenCoverUnimodularityProof
CompactOpenCoverUnimodularityStatement
ModularCompactAverage
QuotientAutomorphismProof
QuotientAutomorphismStatement
QuotientAverageReal
QuotientAveragingKernel
QuotientComplex
QuotientFunctional
QuotientMass
QuotientMeasure
QuotientMeasureExistence
QuotientMeasureExistenceStatement
QuotientMeasurePrerequisites
QuotientPositiveLifting
QuotientTopology
QuotientTranslation
SplitKernelQuotient
```

Prefix `Langlands.ClassFieldTheory.Local.`:

```text
Completion
FiniteArtin
Galois
Norms
ProfiniteReciprocityStatement
ReciprocityRelations
Transfer
Units
WeilAbelianization
WeilReciprocityStatement
```

Prefix `Langlands.Correspondence.`:

```text
AutomorphicRelations
Domains
LocalConventions
OperationCompatibility
SupercuspidalRelations
UnramifiedNormalization
```

Prefix `Langlands.Galois.FiniteField.`:

```text
Comparison
ComparisonProof
Frobenius
```

Prefix `Langlands.Galois.Local.`:

```text
AbsoluteDefinitions
AbsoluteProof
AbsoluteStatement
SpectralDefinitions
SpectralProof
SpectralStatement
```

Prefix `Langlands.Group.`:

```text
HaarModulus
```

Prefix `Langlands.Group.GL.`:

```text
Basic
BlockContractionProof
BlockContractionStatement
BlockIwahoriBasis
BlockIwahoriBasisStatement
BlockIwahoriDefinitions
BlockModulus
BlockModulusHaarProof
BlockModulusHaarStatement
BlockUnipotentCoordinates
BlockUnipotentHaarProof
BlockUnipotentHaarStatement
Blocks
CartanProof
CartanStatement
CompactOpen
CountabilityProof
CountabilityStatement
IntegralSubgroup
InverseTransposeIwahoriProof
InverseTransposeIwahoriStatement
Maps
Nonarchimedean
NonarchimedeanStatement
NormalizedCharacter
OneBlockShape
OppositeBlocks
Padic
PadicBlocks
PadicOppositeBlocks
PadicUpperUnipotent
ParabolicModularCharacter
PrincipalBlockFactorizationProof
PrincipalBlockFactorizationStatement
RankMaps
ReverseBlocks
SingleBlock
Transvection
TriangularParabolic
UnramifiedCharacter
UpperBruhatEmbedding
UpperBruhatPivotProof
UpperBruhatPivotStatement
UpperBruhatProof
UpperBruhatStatement
UpperUnipotent
```

Prefix `Langlands.HarmonicAnalysis.`:

```text
AlgebraicIntegral
AlgebraicIntegrand
Basic
Conductor
FiniteProductMeasureScaling
HaarConjugacy
PadicHaarScalingStatement
PadicRectangularHaarScalingProof
PadicScalarHaarScalingProof
TriangularTranslationProof
TriangularTranslationStatement
```

Prefix `Langlands.LocalFactor.`:

```text
RankOne
```

Prefix `Langlands.LocalField.`:

```text
Canonical
Definitions
Topology
Uniformizer
```

Prefix `Langlands.LocalField.Normalization.`:

```text
Definitions
Proof
Statement
```

Prefix `Langlands.Representation.`:

```text
OrbitSpan
SubrepresentationLattice
```

Prefix `Langlands.Representation.Category.`:

```text
Abelian
Basic
ClassInvariants
ConstituentDichotomy
ConstituentDichotomyStatement
Contragredient
FiniteIndexRestriction
FiniteIndexSemisimplicity
FiniteIndexSemisimplicityStatement
RestrictionSubquotients
Subquotients
Twist
```

Prefix `Langlands.Representation.Classification.`:

```text
CanonicalConstituents
CommonImageMultiplicityOneProof
CommonImageMultiplicityOneStatement
ConstituentRelations
Cosocle
CuspidalIntegralTwistFreenessProof
CuspidalIntegralTwistFreenessStatement
CuspidalJacquetFunctorExactnessProof
CuspidalJacquetFunctorExactnessStatement
CuspidalJacquetFunctors
CuspidalJacquetMultiplicityProof
CuspidalJacquetMultiplicityStatement
CuspidalProductContragredient
Essential
HeadQuotientCriterionProof
HeadQuotientCriterionStatement
MultiplicityOneConstituentProof
MultiplicityOneConstituentStatement
OppositeCuspidalJacquetFiltrationProof
OppositeCuspidalJacquetFiltrationStatement
OppositeJacquetQuotientDetectionProof
OppositeJacquetQuotientDetectionStatement
OppositeJacquetReciprocity
OppositeSupportJacquetAdapter
SegmentConstituentStatement
SegmentHeadContragredient
SegmentHeadDecreasingSocle
SegmentInductionAdmissibilityProof
SegmentInductionAdmissibilityStatement
SegmentJacquetMultiplicityProof
SegmentJacquetMultiplicityStatement
SegmentJacquetReversal
SegmentSpecialConstituentExistenceProof
SegmentTensorReversalProof
SegmentTensorReversalStatement
SegmentTensorStabilizerProof
SegmentTensorStabilizerStatement
Segments
Supercuspidal
SupercuspidalContragredient
SupercuspidalContragredientAux
SupercuspidalContragredientProof
SupercuspidalContragredientStatement
SupercuspidalSupport
SupercuspidalTwist
Tempered
TemperedInductionStatement
TemperedSupportStatement
UpperCuspidalJacquetMultiplicityProof
UpperCuspidalJacquetMultiplicityStatement
UpperJacquetSubrepresentationDetectionProof
UpperJacquetSubrepresentationDetectionStatement
```

Prefix `Langlands.Representation.Compact.`:

```text
Definitions
FiniteMean
OrbitMeanTranslation
ProjectionProof
ProjectionStatement
SurjectivityProof
SurjectivityStatement
```

Prefix `Langlands.Representation.CompactCoefficient.`:

```text
AdmissibleComplement
AdmissibleLifting
AdmissibleRetraction
AmbientProjector
Classes
ConditionalProjection
FixedVectorsFiniteDimensional
GroupTransport
Isotypic
IsotypicTransport
NormalSubgroupDecomposition
OrthogonalProjectorFamily
SelectedAssembly
SelectedBlock
SelectedConjugation
SelectedCoverage
SelectedProjector
SemisimplicityProof
SemisimplicityStatement
TotalCompactness
TotalProjector
```

Prefix `Langlands.Representation.Conductor.`:

```text
Congruence
Definitions
PrincipalCongruence
PrincipalCongruenceBasisProof
PrincipalCongruenceBasisStatement
```

Prefix `Langlands.Representation.CuspidalSupport.`:

```text
AssociatedAssembly
AssociatedConditional
AssociatedGeometricPieceVanishingProof
AssociatedGeometricPiecesEquivalenceProof
AssociatedGeometricPiecesProof
AssociatedGeometricPiecesStatement
AssociatedProof
AssociatedRankZero
AssociationForwardHomProof
AssociationForwardHomSupport
AssociationForwardStatement
AssociationLawsProof
AssociationLawsStatement
AssociationReduction
BlockMap
BlockPermutation
BlockWeylTransport
CentralShift
ConstituentComplement
ConstituentComplementStatement
ConstituentFiniteTypes
ConstituentInduction
ConstituentInductionStatement
ConstituentProof
ConstituentRankZero
ConstituentSemisimple
ConstituentSemisimpleStatement
CuspidalBlockIsolationProof
CuspidalBlockIsolationStatement
CuspidalEmbeddingProof
CuspidalTensorAssociationProof
CuspidalTensorProof
CuspidalTensorStatement
DeterminantUnit
DeterminantUnitCartanSupport
DeterminantUnitCentralCompactnessProof
DeterminantUnitCentralCompactnessStatement
DeterminantUnitFiniteRestriction
DeterminantUnitStructureProof
DeterminantUnitStructureStatement
DistinctTensorStabilizerProof
DistinctTensorStabilizerStatement
DualAveraging
FiltrationQuasicuspidality
FiniteBlockShapes
GroupTransport
HarishChandraAssembly
HarishChandraBoundaryProof
HarishChandraBoundaryStatement
HarishChandraConverseProof
HarishChandraConverseStatement
HarishChandraForwardProof
HarishChandraStatement
InducedJacquetCount
InducedJacquetEvaluation
JacquetInductionStatement
JacquetLengthDetector
JacquetSubquotientProof
JacquetSubquotientStatement
JacquetVanishingHelpers
JacquetVanishingSubgroups
LeviAssociation
LeviDecompositionAssembly
LeviDefinitions
LeviGapVanishing
LeviSplitContraction
MinimalConjugatingCosetsProof
MinimalJacquetProof
MinimalJacquetStatement
MinimalWeylTransportProof
NaturalProjectorDecomposition
NormalizedCuspidalInductionStatement
PointwiseProjectorSum
QuasicuspidalEmbeddingProof
QuasicuspidalLeviAdmissibilityProof
QuasicuspidalPrerequisitesStatement
QuasicuspidalStructureStatement
TotalConjugatingCountProof
TotalConjugatingCountStatement
ZeroRankEmbeddingProof
```

Prefix `Langlands.Representation.Dual.`:

```text
Definitions
```

Prefix `Langlands.Representation.Exponents.`:

```text
Central
DualJacquet
DualJacquetStatement
Jacquet
NilpotenceIndex
ParabolicPair
UnitaryDualJacquetSupportAdapters
```

Prefix `Langlands.Representation.Filtration.`:

```text
CoinvariantVanishingStatement
Definitions
FiniteFamilyMultiplicityProof
FiniteFamilyMultiplicityStatement
GradedRefinementProof
GradedRefinementStatement
IntervalLiftProof
IntervalLiftStatement
IrreducibleMultiplicityProof
IrreducibleMultiplicityStatement
IsoTransport
JordanHolderComparisonProof
JordanHolderStatement
JordanHolderTransportProof
LengthCriterionProof
LengthCriterionStatement
LengthTwoMatching
LengthTwoMatchingStatement
MultiplicityAdditivityProof
MultiplicityAdditivityStatement
MultiplicityIndependenceProof
MultiplicityStatement
MultiplicityTransportProof
MultiplicityTransportStatement
ObjectDefinitions
ObjectTransport
QuotientFirstIso
RepresentationLength
SimpleMapMultiplicityDetectionProof
SimpleMapMultiplicityDetectionStatement
SubquotientAlgebraProof
SubquotientAlgebraStatement
Transport
ZeroFactorDeletionProof
ZeroFactorDeletionStatement
```

Prefix `Langlands.Representation.Geometric.`:

```text
BlockIntersectionSplitting
BlockSixDecomposableProof
BlockSixDecomposableStatement
BruhatDescent
BruhatMatrixExistenceProof
BruhatMatrixStatement
BruhatWeylReflectionProof
ClosedSubgroupAssembly
ClosedSubgroupDefinitions
ClosedSubgroupMackeyProof
ClosedSubgroupStatement
CoarseLeviReversal
CompactOrbitRestriction
CompactSmoothComparison
ConditionalAssembly
CorrectionSubgroupCoordinates
CorrectionSubgroupDiagonalHaarProof
CorrectionSubgroupDiagonalHaarStatement
CosetAction
CosetOrbitHomeomorph
CosetOrbitOrdering
FlattenedLevi
GeneralCorrectionCharacters
GeneralIntersectionNormalizers
GeneralIntersections
GeometricLemmaProof
GeometricLemmaStatement
IntersectionLeviDiagonalCharacterProof
IntersectionLeviDiagonalCharacterStatement
IntersectionLeviModulusBalance
IntersectionTransport
MonotoneBlocksProof
MonotoneBlocksStatement
OrbitRepresentatives
OrbitRestriction
OrbitSectionExtensionProof
OrbitSectionExtensionStatement
PadicCorrectionCancellationProof
PadicCorrectionCancellationStatement
PadicParabolicBruhatProof
ParabolicOrbitCoefficientComparison
ParabolicOrbitCompactComparison
ParabolicOrbitComparisonData
ParabolicOrbitHaarComparison
ParabolicOrbitHaarRatio
ParabolicOrbitHaarTransport
ParabolicOrbitInductionTransport
ParabolicOrbitJacquet
ParabolicOrbitJacquetProof
ParabolicOrbitJacquetStatement
ParabolicOrbitMeasureData
ParabolicOrbitNestedAction
ParabolicOrbitNormalization
ParabolicOrbitNormalizedCoefficient
ParabolicOrbitSectionComparison
ParabolicOrbitStagesCoefficient
ParabolicSupportFiltration
ParabolicSupportGradedProof
ParabolicSupportGradedStatement
ParabolicSupportJacquetProof
ParabolicSupportJacquetStatement
ParabolicSupportTransport
RefinedPositiveCharacter
RefinementDefinitions
RefinementFunctors
RefinementUniqueness
SmoothSupportFiltration
StandardIntersectionsProof
WeylDefinitions
WeylMinimalRepresentativeProof
WeylStatement
WeylUniquenessProof
WeylUniquenessStatement
```

Prefix `Langlands.Representation.Hecke.`:

```text
ActionIntegrand
ActionProjection
CommonInvarianceProof
CommonInvarianceStatement
Convolution
Corner
CornerAction
DoubleCoset
IntegratedAction
IntegratedConvolution
NormalizedIndicator
TestFunction
```

Prefix `Langlands.Representation.Induction.`:

```text
BlockCharacterAbsorption
BlockEquivalence
BlockFactors
CharacterTwistProof
CompactAutomorphism
CompactAutomorphismIntegralProof
CompactAutomorphismIntegralStatement
CompactBilinearPairing
CompactCoinvariantBijectivityProof
CompactCoinvariantBijectivityStatement
CompactCoinvariantIntegral
CompactCoinvariantLocalInverseProof
CompactCoinvariantLocalInverseStatement
CompactLocalSection
CompactLocalSectionSpanningProof
CompactLocalSectionSpanningStatement
CompactLocallyConstant
CompactPairingDuality
CompactQuotientCutoff
CompactQuotientProof
CompactScalarProof
CompactScalarStatement
CompactSurjectivityProof
CompactSurjectivityStatement
CompactTransitivityProof
CompactTransitivityStatement
ConjugateParabolic
Definitions
Equivalences
InverseTranspose
NormalCoinvariantKernelProof
NormalCoinvariantKernelStatement
NormalCoinvariantMap
NormalCoinvariantProof
NormalCoinvariantStatement
NormalSplitComparison
OppositeParabolic
OppositeProductReversalProof
OppositeProductReversalStatement
Parabolic
PiScalarIntegral
SplitKernelCompact
SplitKernelCovariance
SplitKernelEquivariant
SplitKernelIntegral
SplitQuotientProof
SplitQuotientStatement
SplitStagesComparison
SplitStagesRetraction
StructuralStatement
SurjectivityProof
SurjectivityStatement
```

Prefix `Langlands.Representation.Jacquet.`:

```text
BlockCompressionProof
BlockCompressionStatement
BlockPowerKernelProof
CanonicalLiftBijectivityProof
CanonicalLiftDefinitions
CanonicalLiftGroupTransportProof
CanonicalLiftGroupTransportStatement
CanonicalLiftIntertwinerNaturalityProof
CanonicalLiftIntertwinerNaturalityStatement
CanonicalLiftStatement
CharacterTwistEquiv
Coinvariants
CompactCompressionStableDualityProof
CompactCompressionStableDualityStatement
CompressionStabilizationProof
CompressionStabilizationStatement
ExactProof
ExactStatement
Normalized
OppositeCanonicalLiftProof
OppositeCanonicalLiftStatement
Parabolic
PositiveCharacter
ReciprocityProof
ReciprocityStatement
RefinedOppositeCanonicalLiftProof
RefinedOppositeCanonicalLiftStatement
RefinedOppositeCompressionProof
RefinedOppositeCompressionStatement
RefinedOppositePowerKernelProof
RefinedOppositeStableImageProof
RefinedUpperCanonicalLiftProof
SmoothTwist
StablePairingProof
```

Prefix `Langlands.Representation.MatrixCoefficient.`:

```text
Definitions
LawsProof
LawsStatement
ModuloCenter
```

Prefix `Langlands.Representation.Parabolic.`:

```text
AdmissibilityStatement
FlattenedRefinementModulusCalculation
GeometricPrerequisitesStatement
LeviBridges
LeviInflationAdmissibilityProof
NaturalFirstAdjointness
NaturalInductionDualityFromScalar
NaturalInductionDualityProof
NaturalInductionDualityStatement
NaturalJacquetDualityProof
NaturalJacquetDualityStatement
NormalizedAdmissibilityProof
NormalizedInductionStatement
NormalizedJacquetAdmissibilityProof
NormalizedJacquetExactnessProof
NormalizedJacquetStatement
OppositeJacquetAdmissibilityProof
OppositeJacquetAdmissibilityStatement
OppositeRefinementDefinitions
OppositeRefinementFunctors
OppositeRefinementTransitivityProof
OppositeRefinementTransitivityStatement
QuotientCompactProof
RefinedInductionAdmissibility
RefinedInductionTensorNormalization
RefinedInductionTensorStatement
RefinementCharacter
RefinementComposition
RefinementPreimage
SecondAdjointnessAssembly
SecondAdjointnessProof
SecondAdjointnessStatement
StandardOppositeJacquetAdmissibilityProof
UnipotentFiniteContainment
```

Prefix `Langlands.Representation.RankinSelberg.`:

```text
GeneralLinearUnimodularity
Measures
UnimodularityStatement
UnipotentUnimodularity
```

Prefix `Langlands.Representation.Schur.`:

```text
CountableDimensionProof
CountableDimensionStatement
```

Prefix `Langlands.Representation.Smooth.`:

```text
Definitions
SmallRealizationProof
SmallRealizationStatement
```

Prefix `Langlands.Representation.Smooth.Admissibility.`:

```text
CofinalProof
CofinalStatement
EmbeddingProof
EmbeddingStatement
EquivalenceProof
EquivalenceStatement
Extension
```

Prefix `Langlands.Representation.Smooth.Contragredient.`:

```text
AdmissibleDualityProof
AdmissibleDualityStatement
CompactDualityProof
CompactDualityStatement
Definitions
ExactProof
ExactStatement
FixedVectorsDefinitions
HomDualityProof
HomDualityStatement
InvariantPairingProof
InvariantPairingStatement
LawsProof
LawsStatement
```

Prefix `Langlands.Representation.Smooth.Factorization.`:

```text
MultiplicityDefinitions
```

Prefix `Langlands.Representation.Smooth.FixedVectors.`:

```text
Definitions
Detection
FiniteTypes
FiniteTypesStatement
GenerationInheritance
GenerationInheritanceStatement
LawsProof
LawsStatement
OrderProof
OrderStatement
```

Prefix `Langlands.Representation.Smooth.Schur.`:

```text
Proof
Statement
```

Prefix `Langlands.Representation.Smooth.SmoothPart.`:

```text
BasicProof
BasicStatement
Definitions
FixedVectorsDefinitions
```

Prefix `Langlands.Representation.Smooth.Transfer.`:

```text
GroupEquivalence
PullbackProof
PullbackStatement
SubquotientProof
SubquotientStatement
```

Prefix `Langlands.Representation.Tensor.`:

```text
Filtration
Finite
FiniteEquivalences
FiniteProperties
FiniteRegrouping
ProductFiltration
SmoothDual
SmoothDualInjectivityProof
SmoothDualInjectivityStatement
SmoothDualSurjectivityProof
SmoothDualSurjectivityStatement
```

Prefix `Langlands.Representation.Twist.`:

```text
AdmissibilityProof
AdmissibilityStatement
AlgebraProof
AlgebraStatement
ContinuousCharacterProof
ContinuousCharacterStatement
Definitions
DualProof
DualStatement
RealPower
SmoothPartDefinitions
SmoothProof
SmoothStatement
SubquotientDefinitions
SubquotientProof
SubquotientStatement
```

Prefix `Langlands.Representation.Unitary.`:

```text
Basic
```

Prefix `Langlands.Representation.Unramified.`:

```text
Eigenvalues
HeckeOperators
PrincipalSeries
SphericalClassificationStatement
SphericalConstituentExistenceProof
```

Prefix `Langlands.Representation.Whittaker.`:

```text
Iwasawa
```

Prefix `Langlands.Topology.`:

```text
CompactNormCharacter
```

Prefix `Langlands.Topology.CompactOpen.`:

```text
ConjugationStabilizer
NeighborhoodBasis
NeighborhoodBasisStatement
```

Prefix `Langlands.Topology.GroupAction.`:

```text
FiniteOrbitProof
FiniteOrbitStatement
```

Prefix `Langlands.Topology.Nonarchimedean.`:

```text
Subgroup
```

Prefix `Langlands.VirtualRepresentation.`:

```text
Exact
ExactTwist
Integral
```

Prefix `Langlands.Weil.`:

```text
Algebraic
AlgebraicProof
Pullback
Topology
TopologyProof
```

Prefix `Langlands.Weil.Local.`:

```text
Assembly
DegreeCharacters
Parameters
ResidueCharacters
```

Prefix `Langlands.Weil.Representation.`:

```text
Basic
CharacterLine
Continuity
ContinuityProof
Determinant
DirectSum
Dual
DualClasses
IsomorphismInvarianceProof
OperationClosureProof
Operations
Predicates
Twist
TwistClasses
TwistProperties
```

Prefix `Langlands.WeilDeligne.`:

```text
Basic
DirectSum
Dual
ParameterRelations
Parameters
Twist
```

## External import roots

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.Algebra.NonUnitalHom
Mathlib.Algebra.Algebra.NonUnitalSubalgebra
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.GroupWithZero.Action
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.DirectSum.Module
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Field.Subfield.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Pi.Lemmas
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Subgroup.Pointwise
Mathlib.Algebra.Group.TypeTags.Finite
Mathlib.Algebra.Group.TypeTags.Hom
Mathlib.Algebra.Module.Projective
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Cardinality
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Matrix.Normed
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Analysis.SpecialFunctions.Sqrt
Mathlib.Analysis.SpecificLimits.Basic
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Abelian.Subcategory
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
Mathlib.CategoryTheory.Skeletal
Mathlib.CategoryTheory.Whiskering
Mathlib.Combinatorics.Enumerative.Composition
Mathlib.Data.ENat.Basic
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Quotient
Mathlib.Data.Fintype.Sort
Mathlib.Data.Int.Cast.Lemmas
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.Data.PNat.Basic
Mathlib.Data.Set.Card
Mathlib.Data.Sym.Basic
Mathlib.Data.ZMod.Basic
Mathlib.FieldTheory.AbsoluteGaloisGroup
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.Finite.Extension
Mathlib.FieldTheory.Galois.Profinite
Mathlib.FieldTheory.PrimitiveElement
Mathlib.GroupTheory.Abelianization.Defs
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.FiniteIndexNormalSubgroup
Mathlib.GroupTheory.GroupAction.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Defs
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Index
Mathlib.GroupTheory.OrderOfElement
Mathlib.GroupTheory.QuotientGroup.Defs
Mathlib.GroupTheory.Subgroup.Center
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.GroupTheory.Transfer
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.DirectSum.Finite
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
Mathlib.LinearAlgebra.Finsupp.LinearCombination
Mathlib.LinearAlgebra.Finsupp.VectorSpace
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.SchurComplement
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Dual
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.Projection
Mathlib.LinearAlgebra.Quotient.Basic
Mathlib.LinearAlgebra.Semisimple
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.OpenPos
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.CompactlyGenerated.Basic
Mathlib.Order.Hom.Set
Mathlib.Order.WithBot
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Equiv
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.Algebraic.LinearIndependent
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Jacobson.Semiprimary
Mathlib.RingTheory.Length
Mathlib.RingTheory.Nilpotent.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.Norm.Transitivity
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Extension
Mathlib.RingTheory.Valuation.Integral
Mathlib.RingTheory.Valuation.LocalSubring
Mathlib.RingTheory.Valuation.RamificationGroup
Mathlib.Tactic.Group
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Tactic.NormNum
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
Mathlib.Topology.Algebra.ConstMulAction
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.ClosedSubgroup
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.GroupWithZero
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Ring.Ideal
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.Lemmas
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.Int
Mathlib.Topology.Instances.Matrix
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
Mathlib.Topology.Order.Compact
Mathlib.Topology.Separation.Profinite
Mathlib.Topology.UrysohnsLemma
```
