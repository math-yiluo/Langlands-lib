# Actual quotient occurrences in binary-product derivatives

Author: Worker 357.

This internal construction returns a surjection from an actual invariant
subspace of a binary-product derivative onto a supplied quotient of a
first-factor derivative. The second factor is differentiated to full order
and is assumed nonzero there. The construction selects the corresponding
feasible grade of the published all-rank Leibniz filtration and contracts
its rank-zero second tensor factor.

## Parameters and actual constructions

Fix arbitrary `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, its supplied
topological data `T`, and a bundled continuous nontrivial unitary additive
character `ψ` for `T.topology`. The field universe `uF` and original carrier
universe `uV` remain independent. All declarations are under
`Langlands.Derivative`.

`leibnizSmoothPieceQuotient` takes ranks `a,b`, an order `d ≤ a+b`, a
specified feasible index `x : LeibnizIndex a b d`, and actual smooth
representations `A,B` of `GL_a,GL_b` with carriers in `Type uV`. Write
`J=(A × B)^(d)`, in carrier universe `max uF uV`. Its result is the
dependent pair

```text
Σ S : Subrepresentation J.representation,
  {q : SmoothRep.subrepresentation J S ⟶
       (leibnizSmoothPiece T ψ a b d x).obj (A,B) //
       Function.Surjective (SmoothRep.hom q)}.
```

Here `×` denotes the literal `T.binaryNormalizedProductFunctor`, and the
derivative denotes `generalLinearDerivative` with the supplied topology,
character, rank and valid order. The target is exactly the existing smooth
Leibniz piece: the two factor derivatives, their binary normalized product,
and the published rank cast. The result retains an invariant subspace and
an actual quotient map, rather than an equality of classes.

The primary constructor `rightTopDerivativeQuotientOccurrence` takes
`r ≤ a`, representations `A,B` with carriers in `Type (max uF uV)`, and
an actual smooth `GL_((a+b)-(r+b))` representation `Q` in that same carrier
universe. Its two substantive premises are:

- a supplied smooth morphism `q` from the rank-cast `A^(r)` onto `Q`,
  together with `Function.Surjective (SmoothRep.hom q)`;
- `Nontrivial ((generalLinearDerivative T ψ b b le_rfl).obj B)`,
  the nontriviality of the full order-`b` derivative of `B`.

The cast in the source of `q` is
`generalLinearRankCast T (by omega : a-r=(a+b)-(r+b))`.
The constructor returns

```text
Σ S : Subrepresentation ((A × B)^(r+b)).representation,
  {f : SmoothRep.subrepresentation ((A × B)^(r+b)) S ⟶ Q //
       Function.Surjective (SmoothRep.hom f)}.
```

`rightTopDerivativeQuotient_isSubquotient` packages the returned maps as
the existing actual relation
`SmoothRep.IsSubquotient Q ((A × B)^(r+b))`. It uses the canonical injective
inclusion of `S` and the returned surjection.

All natural ranks and every valid order are covered. In particular, `r=0`,
`r=a`, `a=0`, `b=0` and simultaneous residual rank zero are retained.
No irreducibility, finite length, admissibility, segment or linkage
hypothesis is imposed. `Q` may be reducible or zero. The nontrivial top
derivative premise is supplied, not derived. No relation between `uF`
and `uV` is introduced; the primary constructor specializes the general
grade constructor to input universe `max uF uV`, which is stable under
the product's further maximum with `uF`.

## Implemented maps and proofs

For the first constructor, the published unconditional
`generalLinearDerivativeLeibnizFiltration F T`, through its `.filtration`
extractor, gives an enumeration `e` of every feasible index, an actual
filtration `s` of the forgotten product derivative, and natural grade
isomorphisms. Choose `j=e x`. Evaluate the grade isomorphism at `(A,B)`
and compose it with the equality isomorphism from
`e.symm (e x)=x`. This gives an actual representation equivalence from
the selected grade to the requested piece.

Set `S=(s.step j.succ).obj (A,B)`. The existing
`RepSubfunctor.quotientNatProjection`, evaluated at `(A,B)`, is the
canonical surjection from this upper step to its successive quotient.
The quotient is definitionally `s.graded j` at that object. Compose its
underlying intertwiner with the grade equivalence, then use
`SmoothRep.ofHom` with the explicit smooth source and target. Its
surjectivity is the composite of the canonical quotient's surjectivity
and the equivalence's surjectivity.

The filtration and its isomorphisms are obtained from existential
propositions. The construction first builds `Nonempty` of the desired
dependent pair and then applies `Classical.choice`. Thus it returns
actual data without eliminating an existential proposition directly
into a type.

The private helper `rightZeroProductQuotient` deals with the tensor
contraction. Given `b=0`, eliminate that equality. The published
`T.binaryRightZeroTensorEquiv` identifies the actual binary product
with the tensor representation on which the first factor acts and
the second factor is trivial. It covers also `a=0`, where the actual
`GL_0` actions are trivial. The supplied nontriviality of the second
carrier makes `BinaryTensor.firstFactorQuotient` available. This chooses
a nonzero vector and a complex-linear functional taking value one on
it, then contracts the second tensor coordinate. On pure tensors its
value is `φ(w) • v`; each `v` has preimage `v ⊗ w`. Its equivariance
holds because only the first tensor coordinate acts.

The rank-zero tensor action is the first-factor action composed with
the equality reindexing of `GL_(a+0)` to `GL_a`. The helper simplifies
that reindexing to the identity, retains the contraction's actual
linear map and equivariance proof, and composes with the published
binary tensor equivalence. The result is an actual surjection to the
rank-cast first factor. Both its source and its full second carrier
remain present; there is no dimension-one replacement.

For the primary constructor choose the feasible pair `x=(r,b)` in
`LeibnizIndex a b (r+b)`. Put `DA=A^(r)` and `DB=B^(b)`. Its piece is

```text
rank-cast (DA × DB), with ranks (a-r) and (b-b)=0.
```

Apply the rank-zero helper using the supplied nontriviality of `DB`.
Map the resulting contraction through the piece's prescribed outer
rank cast. The published `generalLinearRankCast_trans` identifies the
two successive casts of `DA` with the single cast in the source of
the supplied `q`. Its equality isomorphism gives the intervening
bijective map. Compose with `q` to obtain a surjection from the
piece onto `Q`.

The other private helper, `rankCast_surjective`, proves preservation
of surjectivity by eliminating the rank equality; the cast functor
then becomes the identity. Surjectivity of the intervening equality
isomorphism and the given surjectivity of `q` prove surjectivity of
the composite. Finally apply `leibnizSmoothPieceQuotient` to `x` and
compose its actual projection with this piece-to-`Q` map. This yields
the asserted invariant subspace and surjection. The final theorem
uses `SmoothRep.isSubquotient_iff_exists` with the canonical subtype
inclusion and these maps.

## Provenance and independence

This is derived internal material: it composes published actual
constructions and elementary quotient, tensor and equality-transport
arguments. It does not transcribe an additional literature theorem.
The two direct imports and their used interfaces are:

| Module, after `Langlands.Representation.` | Used construction |
| --- | --- |
| `Derivative.LeibnizConstituentExtraction` | Existing smooth Leibniz piece and the published general Leibniz filtration and its full feasible enumeration |
| `Tensor.OneFactorQuotient` | Actual equivariant contraction onto the acting tensor factor with its surjectivity proof |

The first import's extraction theorems are not invoked here. The
published Leibniz proof supplies an actual natural finite filtration,
assembled from the general mirabolic two-orbit sequence and the proved
left and right mixed-product derivative comparisons. Its boundary
branches use actual tensor models. Its original-source correspondence,
normalization and underlying general derivative proofs are documented in
[GeneralLinearDerivativeLeibnizFiltrationProof](GeneralLinearDerivativeLeibnizFiltrationProof.md)
and [LeibnizConstituentExtraction](LeibnizConstituentExtraction.md).
The contraction's underlying general linear algebra is documented in
[OneFactorQuotient](../Tensor/OneFactorQuotient.md).

The full host task remains
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`. Trusted operator decisions
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md)
and
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md)
permit independently proved and published general derivative
infrastructure while preserving all its exclusions. The further
support-only ruling
[30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
and the limitations in
[ed80148e21e7523abfc048f455e98eb0](/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md),
[2b33898bdd0a5ff1b9031be5155a06f0](/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md)
and
[ca18fd5005bf5e12a3f7cade18dca865](/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md)
are retained. No support-bound proof or restricted intermediate is an
input to this module.

The used proof bodies consist of the general filtration, its canonical
quotient projection and grade isomorphism, the actual binary rank-zero
equivalence, the one-factor contraction, equality transport, and the
actual subquotient presentation. In particular:

- Neither Ze80 §§3.5/9.6 nor any segment derivative formula or proof
  successor is imported or used. No derivative of a segment is
  identified, asserted irreducible, or given a multiplicity.
- The excluded segment/head/socle Jacquet formulas, exponent formula
  and tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`,
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`,
  `55ad1e10-62d8-46b7-a081-909ef0056426`,
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`, the segment-socle product
  criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, and the
  segment-socle part of task `8e5b4563` supply no input.
- The host criterion in either direction and parent uniqueness
  `30341ae4-65f2-4a0e-9283-763db01a409e` supply no input. Neither do
  multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
  ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
  quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
  ordered conversion `8252833d-c269-41a9-824c-5879e531b23b`,
  tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`,
  square-integrable classification `1cb45da2-7007-4351-a694-594fb148b8d1`,
  square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`,
  or regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`.
- `SegmentHeadSupportStep`, `SegmentHeadJacquetReduction`,
  `core_mid`, the restricted length-two consequence, and
  `TwoSupercuspidalProductStructureProof` are absent. The limited
  reducibility permission for the separate support proof is unused.
- The classification-named inherited modules are exactly
  `ConstituentRelations`, `Segments`, `Supercuspidal`,
  `SupercuspidalContragredientAux`,
  `SupercuspidalContragredientStatement`, `SupercuspidalSupport`
  and `SupercuspidalTwist`. They contribute definitions and general
  subquotient, equivalence and twist infrastructure, with no
  excluded classification or segment conclusion.
- No Whittaker/Levi/supercuspidal coinvariant-finiteness or dependent
  mirabolic-finite-length conclusion is used. No pending candidate
  supplies an imported pair or proof dependency.

This focused constructor does not complete the special-head product
irreducibility criterion. Its quotient and nonzero-top premises remain
explicit obligations for applications. It supplies neither an occurrence
for a linked pair without those inputs, nor replacement nonoccurrence,
nor the linked converse or the reduction from an arbitrary family.

## Complete import inventory and validation

Recursive native traversal at published Library commit
`442ff746325df5b6d721fee75d430a65c33d09f0` finds 368 project modules
including this entry and 145 distinct external frontier imports. All 367
inherited Lean/Markdown pairs are nonempty and byte-identical to that
Library. No inherited pair is edited and no missing module is supplied
by staging. The full code scan, after removing nested comments and
string literals, finds no proof hole, new axiom, prohibited execution
syntax, or match for the inherited excluded-name and task-identifier
inventory. The used-body audit above supplements this scan.

Development compilation `d335e4af-06ac-42ec-9e9a-a51d2f6976da` and the
Lake build and exact declaration inspection
`485914cb-37bf-4023-8a36-76ef5cd0a86a` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` succeed with zero errors and
warnings. Inspection reports a definition with independent level
parameters `uF,uV` and only `propext`, `Classical.choice` and `Quot.sound`.
These are development checks; independent semantic review and Library
publication remain required.

The following grouped inventories expand each prefix with its immediate
module suffixes to give the complete audited module names.

### Project modules

- `Langlands.Analysis.Local`: `CompactOpenCoverUnimodularityProof`, `CompactOpenCoverUnimodularityStatement`, `ModularCompactAverage`, `QuotientAutomorphismProof`, `QuotientAutomorphismStatement`, `QuotientAverageReal`, `QuotientAveragingKernel`, `QuotientComplex`, `QuotientFunctional`, `QuotientMass`, `QuotientMeasure`, `QuotientMeasureExistence`, `QuotientMeasureExistenceStatement`, `QuotientMeasurePrerequisites`, `QuotientPositiveLifting`, `QuotientTopology`, `QuotientTranslation`, `SplitKernelQuotient`.
- `Langlands.Group`: `HaarModulus`, `LeftQuotient`.
- `Langlands.Group.GL`: `Basic`, `BlockDeterminant`, `BlockModulus`, `Blocks`, `CompactOpen`, `CountabilityProof`, `CountabilityStatement`, `Maps`, `Mirabolic`, `MirabolicMixedOrbitCoverageProof`, `MirabolicMixedOrbitCoverageStatement`, `MirabolicMixedOrbitData`, `MirabolicMixedOrbitRadicals`, `MirabolicMixedOrbitSectionCoefficients`, `MirabolicMixedOrbitSections`, `MirabolicMixedOrbitSpecializations`, `MirabolicMixedOrbitStages`, `MirabolicMixedProductSubgroups`, `MirabolicModularCharacterProof`, `MirabolicModularCharacterStatement`, `MirabolicModulusProof`, `MirabolicModulusStatement`, `MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `PadicOppositeBlocks`, `PadicUpperUnipotent`, `RankMaps`, `RankReindex`, `ReindexCongr`, `ReverseBlocks`, `TriangularParabolic`, `UpperUnipotent`, `UpperUnipotentCompactContainmentProof`, `UpperUnipotentCompactContainmentStatement`.
- `Langlands.HarmonicAnalysis`: `AlgebraicIntegral`, `AlgebraicIntegrand`, `Basic`, `Conductor`, `HaarConjugacy`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`.
- `Langlands.LocalFactor.Harmonic`: `Statement`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Topology`.
- `Langlands.LocalField.Normalization`: `Definitions`, `Proof`, `Statement`.
- `Langlands.Representation`: `OrbitSpan`.
- `Langlands.Representation.Category`: `Abelian`, `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Classification`: `ConstituentRelations`, `Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, `SupercuspidalSupport`, `SupercuspidalTwist`.
- `Langlands.Representation.Compact`: `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.Conductor`: `Congruence`.
- `Langlands.Representation.CuspidalSupport`: `LeviDefinitions`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeExactnessProof`, `GeneralLinearDerivativeExactnessStatement`, `GeneralLinearDerivativeLeibnizBoundary`, `GeneralLinearDerivativeLeibnizFiltrationProof`, `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeftMixedProductDerivativeProof`, `LeftMixedProductHigher`, `LeftMixedProductVanishing`, `LeftMixedProductZeroRank`, `LeibnizConstituentExtraction`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizPositiveGluing`, `LeibnizQuotientOccurrence`, `LeibnizQuotientPiece`, `LeibnizRankZeroBoundary`, `LeibnizRankZeroGluing`, `LeibnizRestrictionCompat`, `LeibnizRestrictionExact`, `LeibnizZeroFirstPiece`, `LevelCalculus`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionProof`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicDeterminant`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusExactnessProof`, `MirabolicMinusExactnessStatement`, `MirabolicMixedOrbitCharacters`, `MirabolicPhiMinusMackey`, `MirabolicPlus`, `MirabolicProductMinusBoundary`, `MirabolicProductMinusCompatibilityStatement`, `MirabolicProductMinusLeftPhi`, `MirabolicProductMinusLeftPhiCoefficient`, `MirabolicProductMinusLeftPhiCompactComparison`, `MirabolicProductMinusLeftPhiHaar`, `MirabolicProductMinusLeftPhiHostTransport`, `MirabolicProductMinusLeftPhiIdentityComparison`, `MirabolicProductMinusLeftPhiInductionNormalization`, `MirabolicProductMinusLeftPhiLocalization`, `MirabolicProductMinusLeftPhiMackeyLocalization`, `MirabolicProductMinusLeftPhiNormalization`, `MirabolicProductMinusLeftPhiNormalizedSection`, `MirabolicProductMinusLeftPhiSection`, `MirabolicProductMinusLeftPhiSourceAction`, `MirabolicProductMinusLeftPhiSourceComparison`, `MirabolicProductMinusLeftPhiStagesComparison`, `MirabolicProductMinusLeftPsi`, `MirabolicProductMinusLeftPsiInduction`, `MirabolicProductMinusPhiKernelComparison`, `MirabolicProductMinusRightBoundary`, `MirabolicProductMinusRightPhi`, `MirabolicProductMinusRightPhiAssembly`, `MirabolicProductMinusRightPhiCycle`, `MirabolicProductMinusRightPhiCycleCoefficient`, `MirabolicProductMinusRightPhiCycleGroups`, `MirabolicProductMinusRightPhiIdentity`, `MirabolicProductMinusRightPhiIdentityCoefficient`, `MirabolicProductMinusRightPhiIdentityGroups`, `MirabolicProductMinusRightPsi`, `MirabolicProductMinusRightPsiCoefficient`, `MirabolicProductMinusRightPsiGroups`, `MirabolicProductMinusRightPsiZero`, `MirabolicProductRestriction`, `MirabolicProductRestrictionCasts`, `MirabolicProductRestrictionFactors`, `MirabolicProductRestrictionMackey`, `MirabolicProductRestrictionOrbits`, `MirabolicProductRestrictionStabilizers`, `MirabolicProductRestrictionStatement`, `MirabolicProductRestrictionTransport`, `MixedProductDerivativeStatement`, `MixedProductRankCast`, `OrderRecursion`, `ProductVanishing`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationProof`, `RightMixedProductDerivativeFiltrationStatement`, `RightMixedProductDerivativePositive`, `RightMixedProductZeroRank`, `ShortExactFunctorLaws`, `ZeroRankTensor`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Filtration`: `ActualGradedExtraction`, `Definitions`, `ExactSmoothSubquotients`, `ExactSmoothTransport`, `GluedFamily`, `GradedRefinementProof`, `GradedRefinementStatement`, `IntervalLiftProof`, `IntervalLiftStatement`, `IsoTransport`, `JordanHolderStatement`, `JordanHolderTransportProof`, `LengthCriterionProof`, `LengthCriterionStatement`, `LengthTwoMatching`, `LengthTwoMatchingStatement`, `ObjectDefinitions`, `ObjectTransport`, `OneStep`, `Precomposition`, `QuotientFirstIso`, `QuotientTail`, `RepresentationLength`, `SmoothGradedObject`, `Splicing`, `SubquotientAlgebraProof`, `SubquotientAlgebraStatement`, `SubsingletonProof`, `Transport`, `VanishingStatement`.
- `Langlands.Representation.Filtration.Splicing`: `Basic`.
- `Langlands.Representation.Geometric`: `ClosedSubgroupAssembly`, `ClosedSubgroupDefinitions`, `ClosedSubgroupMackeyProof`, `ClosedSubgroupStatement`, `CompactOrbitRestriction`, `CosetAction`, `CosetOrbitHomeomorph`, `OrbitRestriction`, `OrbitSectionExtensionProof`, `OrbitSectionExtensionStatement`, `WeylDefinitions`.
- `Langlands.Representation.Induction`: `BinaryPositiveCompact`, `BinaryProduct`, `BlockFactors`, `CharacterTwistProof`, `CompactAutomorphism`, `CompactAutomorphismIntegralProof`, `CompactAutomorphismIntegralStatement`, `CompactCoinvariantBijectivityProof`, `CompactCoinvariantBijectivityStatement`, `CompactCoinvariantIntegral`, `CompactCoinvariantLocalInverseProof`, `CompactCoinvariantLocalInverseStatement`, `CompactLocalSection`, `CompactLocalSectionSpanningProof`, `CompactLocalSectionSpanningStatement`, `CompactLocallyConstant`, `CompactQuotientCutoff`, `CompactQuotientProof`, `CompactSurjectivityProof`, `CompactSurjectivityStatement`, `CompactTransitivityProof`, `CompactTransitivityStatement`, `Definitions`, `InverseTranspose`, `NormalCoinvariantKernelProof`, `NormalCoinvariantKernelStatement`, `NormalCoinvariantMap`, `NormalCoinvariantProof`, `NormalCoinvariantStatement`, `NormalSplitComparison`, `OppositeParabolic`, `Parabolic`, `SplitKernelCharacter`, `SplitKernelCharacterExtension`, `SplitKernelCompact`, `SplitKernelCovariance`, `SplitKernelEquivariant`, `SplitKernelHaarTrivial`, `SplitKernelIntegral`, `SplitKernelLocalizationData`, `SplitKernelSectionAction`, `SplitQuotientProof`, `SplitQuotientStatement`, `SplitStagesCharacterComparison`, `SplitStagesCharacterComparisonStatement`, `SplitStagesCharacterIntegrand`, `SplitStagesComparison`, `SplitStagesRetraction`, `StructuralStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.Jacquet`: `CharacterAveraging`, `CharacterTwistEquiv`, `Coinvariants`, `ExactProof`, `ExactStatement`, `Localization`, `LocalizationExactnessProof`, `LocalizationExactnessStatement`, `LocalizationTransport`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Mirabolic`: `LeftMixedProductSuccessor`, `MixedProducts`.
- `Langlands.Representation.Parabolic`: `GeometricPrerequisitesStatement`, `InductionFactorMatchingProof`, `InductionFactorMatchingStatement`, `InductionSubrepresentation`, `ProductInductionSubrepresentation`, `QuotientCompactProof`.
- `Langlands.Representation.RankinSelberg`: `GeneralLinearUnimodularity`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `Measures`, `QuotientIntegrals`, `UnimodularityStatement`, `UnipotentUnimodularity`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`.
- `Langlands.Representation.Smooth`: `Definitions`, `SmallRealizationProof`, `SmallRealizationStatement`.
- `Langlands.Representation.Smooth.Admissibility`: `CofinalProof`, `CofinalStatement`, `EquivalenceProof`, `EquivalenceStatement`.
- `Langlands.Representation.Smooth.Contragredient`: `CompactDualityProof`, `CompactDualityStatement`, `Definitions`, `FixedVectorsDefinitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Smooth.FixedVectors`: `Definitions`.
- `Langlands.Representation.Smooth.SmoothPart`: `BasicProof`, `BasicStatement`, `Definitions`, `FixedVectorsDefinitions`.
- `Langlands.Representation.Smooth.Transfer`: `PullbackProof`, `PullbackStatement`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Tensor`: `ExternalFiltration`, `ExternalSubrepresentation`, `Filtration`, `Finite`, `FiniteEquivalences`, `FiniteFiltration`, `OneFactor`, `OneFactorQuotient`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Unitary`: `Basic`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`, `Iwasawa`.
- `Langlands.Topology`: `CompactNormCharacter`.
- `Langlands.Topology.CompactOpen`: `ConjugationStabilizer`, `NeighborhoodBasis`, `NeighborhoodBasisStatement`.
- `Langlands.Topology.Nonarchimedean`: `Subgroup`.
- `Langlands.Weil.Representation`: `Basic`, `Determinant`, `IsomorphismInvarianceProof`, `Operations`.

### External import frontier

- `Lean.Elab.Tactic`: `Omega`.
- `Mathlib.Algebra.BigOperators`: `Fin`, `Finprod`, `Pi`.
- `Mathlib.Algebra.BigOperators.Group.Finset`: `Basic`.
- `Mathlib.Algebra.CharP`: `Basic`.
- `Mathlib.Algebra.Group.Equiv`: `TypeTags`.
- `Mathlib.Algebra.Group.Hom`: `Instances`.
- `Mathlib.Algebra.Group.Subgroup`: `Ker`.
- `Mathlib.Algebra.Module`: `ULift`.
- `Mathlib.Algebra.Order.Archimedean`: `Basic`.
- `Mathlib.Algebra.Order.BigOperators.Group`: `Finset`.
- `Mathlib.Algebra.Polynomial`: `Lifts`.
- `Mathlib.Algebra.Ring`: `GeomSum`.
- `Mathlib.Analysis.Complex`: `Basic`, `Circle`.
- `Mathlib.Analysis.Fourier`: `FourierTransform`.
- `Mathlib.Analysis.InnerProductSpace`: `Defs`.
- `Mathlib.Analysis.Matrix`: `MeasurableSpace`.
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
- `Mathlib.Data.ENat`: `BigOperators`.
- `Mathlib.Data.Fin`: `Rev`.
- `Mathlib.Data.Fin.Tuple`: `Basic`.
- `Mathlib.Data.Finset`: `NatAntidiagonal`.
- `Mathlib.Data.Fintype`: `Sum`.
- `Mathlib.Data.Int`: `LeastGreatest`.
- `Mathlib.Data.Matrix`: `Block`.
- `Mathlib.Data.Nat`: `Find`.
- `Mathlib.FieldTheory.Finite`: `Basic`.
- `Mathlib.GroupTheory`: `DoubleCoset`.
- `Mathlib.GroupTheory.Coset`: `Defs`.
- `Mathlib.GroupTheory.GroupAction`: `ConjAct`, `Quotient`.
- `Mathlib.GroupTheory.Subgroup`: `Centralizer`.
- `Mathlib.LinearAlgebra`: `Determinant`, `Isomorphisms`.
- `Mathlib.LinearAlgebra.Basis`: `VectorSpace`.
- `Mathlib.LinearAlgebra.Dimension`: `Constructions`.
- `Mathlib.LinearAlgebra.Dual`: `Lemmas`.
- `Mathlib.LinearAlgebra.FiniteDimensional`: `Defs`.
- `Mathlib.LinearAlgebra.Matrix`: `Block`, `Diagonal`, `Kronecker`, `Permutation`, `Reindex`, `Transvection`.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup`: `Basic`.
- `Mathlib.LinearAlgebra.PiTensorProduct`: `Basic`, `Basis`, `Generators`.
- `Mathlib.LinearAlgebra.TensorProduct`: `RightExactness`.
- `Mathlib.Logic.Equiv.Fin`: `Basic`.
- `Mathlib.MeasureTheory.Constructions`: `Pi`.
- `Mathlib.MeasureTheory.Function`: `LocallyIntegrable`, `SimpleFunc`.
- `Mathlib.MeasureTheory.Group`: `Integral`, `LIntegral`, `ModularCharacter`.
- `Mathlib.MeasureTheory.Integral`: `Marginal`, `Prod`.
- `Mathlib.MeasureTheory.Integral.Bochner`: `Basic`, `ContinuousLinearMap`, `Set`.
- `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani`: `Real`.
- `Mathlib.MeasureTheory.Measure`: `Regular`.
- `Mathlib.MeasureTheory.Measure.Haar`: `Basic`, `DistribChar`, `MulEquivHaarChar`, `Unique`.
- `Mathlib.MeasureTheory.Measure.Typeclasses`: `Finite`.
- `Mathlib.NumberTheory.LocalField`: `Basic`.
- `Mathlib.NumberTheory.Padics`: `LocalField`, `RingHoms`.
- `Mathlib.Order`: `Atoms`.
- `Mathlib.RepresentationTheory`: `Basic`, `Coinduced`, `Coinvariants`, `Intertwining`, `Invariants`, `Irreducible`, `Semisimple`, `Subrepresentation`.
- `Mathlib.RepresentationTheory.Rep`: `Basic`, `Res`.
- `Mathlib.RingTheory`: `FiniteLength`, `Length`.
- `Mathlib.RingTheory.Artinian`: `Module`.
- `Mathlib.RingTheory.DedekindDomain`: `IntegralClosure`.
- `Mathlib.RingTheory.Finiteness`: `Basic`.
- `Mathlib.RingTheory.Flat`: `Basic`.
- `Mathlib.RingTheory.Ideal.Quotient`: `Operations`.
- `Mathlib.RingTheory.Noetherian`: `Basic`, `Defs`.
- `Mathlib.RingTheory.RamificationInertia`: `Basic`.
- `Mathlib.RingTheory.SimpleModule`: `Basic`.
- `Mathlib.RingTheory.Valuation`: `Integral`.
- `Mathlib.Tactic`: `Linarith`, `NoncommRing`.
- `Mathlib.Topology`: `Bases`, `LocallyClosed`, `UrysohnsLemma`.
- `Mathlib.Topology.Algebra`: `ContinuousMonoidHom`, `MulAction`, `OpenSubgroup`, `Support`.
- `Mathlib.Topology.Algebra.Group`: `Basic`, `Matrix`, `OpenMapping`, `Pointwise`, `Quotient`, `Subgroup`, `Units`.
- `Mathlib.Topology.Algebra.Module`: `FiniteDimension`, `ModuleTopology`.
- `Mathlib.Topology.Algebra.Nonarchimedean`: `Basic`.
- `Mathlib.Topology.Algebra.ProperAction`: `Basic`.
- `Mathlib.Topology.Algebra.Ring`: `Compact`.
- `Mathlib.Topology.Algebra.ValuativeRel`: `ValuativeTopology`.
- `Mathlib.Topology.Algebra.Valued`: `NormedValued`.
- `Mathlib.Topology.Baire`: `LocallyCompactRegular`.
- `Mathlib.Topology.Compactness`: `Compact`, `LocallyCompact`, `SigmaCompact`.
- `Mathlib.Topology.Connected`: `TotallyDisconnected`.
- `Mathlib.Topology.ContinuousMap`: `CompactlySupported`.
- `Mathlib.Topology.Homeomorph`: `Lemmas`, `Quotient`.
- `Mathlib.Topology.Instances.NNReal`: `Lemmas`.
- `Mathlib.Topology.LocallyConstant`: `Basic`.
- `Mathlib.Topology.Order`: `Compact`.
