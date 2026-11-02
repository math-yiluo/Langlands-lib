# Actual constituent extraction from a derivative Leibniz filtration

Author: Worker 357.

This internal construction locates an actual irreducible subquotient of a
binary-product derivative in an actual smooth Leibniz piece. It also proves
that both derivative factors of that piece are nonzero. A final corollary
allows an actual subquotient of the source product before differentiation.
The occurrence relation is the existing `SmoothRep.IsSubquotient`, with its
literal subrepresentation and quotient; no virtual occurrence is substituted.

## Parameters and conclusions

Fix arbitrary `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, its supplied
topological data `T`, and a bundled continuous nontrivial unitary additive
character `ψ` for `T.topology`. The field universe `uF` and original carrier
universe `uV` are independent.

Let `a b d : ℕ`, with `hd : d ≤ a + b`. The two supplied smooth complex
representations `A` and `B` are on `GL_a` and `GL_b` and have carriers in
`Type uV`. Their actual binary normalized product and its derivative have
carriers in `Type (max uF uV)`. The supplied irreducible representation `D`
of `GL_((a+b)-d)` has this latter carrier universe. All functors install the
supplied topology.

`leibnizSmoothPiece T ψ a b d x` is a smooth-representation functor on the
entire product category of possible `A,B`. For
`x : LeibnizIndex a b d`, write `(i,j) = x.val`. The existing index subtype
asserts `i ≤ a`, `j ≤ b` and `i+j=d`. The piece is the composite of the two
actual derivatives, the actual binary normalized product, and
`generalLinearRankCast T (leibnizIndices_rank x.property)`:

```text
(A,B) ↦ A^(i) × B^(j) ↦ rank-cast to GL_((a+b)-d).
```

Here the first product lives on `GL_((a-i)+(b-j))`. The rank cast uses the
existing equality `(a-i)+(b-j)=(a+b)-d`. Both derivative carriers remain
present, including when a residual rank is zero. The theorem
`leibnizSmoothPiece_toRep` proves by reflexivity that forgetting this smooth
piece gives exactly the published `leibnizPiece`, with its existing
normalization and cast.

The public extraction lemmas in namespace `Langlands.Derivative` are:

- `exists_leibnizSmoothPiece_subquotient`: if `D` is an actual irreducible
  subquotient of the order-`d` derivative of `A × B`, there is a feasible
  `x` such that `D` is an actual subquotient of that smooth piece.
- `exists_nontrivial_leibnizSmoothPiece_subquotient`: the same assertion,
  retaining the occurrence and also returning `Nontrivial A^(i)` and
  `Nontrivial B^(j)`.
- `exists_leibnizSmoothPiece_subquotient_of_subquotient`: let `Q` be any
  actual subquotient of `A × B`, in carrier universe `max uF uV`. If `D` is
  an actual irreducible subquotient of the order-`d` derivative of `Q`,
  the same feasible index, both nonzero derivative factors, and actual
  piece occurrence exist.

No finite-length, admissibility, segment, linkage or genericity hypothesis
is imposed. All ranks and valid orders are included. Order zero and top
order use the same statements; arbitrary `GL_0` carriers are retained.
There is no claim that a whole piece or a factor derivative is irreducible.
In particular, these lemmas do not yet extract simple constituents from
the two factor derivatives.

## Implemented proof

Apply the published unconditional
`generalLinearDerivativeLeibnizFiltration F T` and its `.filtration`
extractor. This gives an equivalence from the complete feasible index set to
a finite ordinal, an actual `RepFunctorFiltration s` of the literal product
derivative after forgetting smoothness, and natural isomorphisms from its
grades to the corresponding published pieces. All feasible indices occur;
repeated or zero grades are retained.

At the supplied pair `(A,B)`, evaluate each invariant subfunctor `s.step i`.
Its monotonicity and zero and top identities give the object filtration
`t` by `ObjectRepFiltration.ofSubrepresentations`. This evaluation is
performed directly in the proof. The source representation of `t` is
definitionally the representation of the actual smooth product derivative.
The module introduces no separate exported evaluation helper.

The published generic
`ObjectRepFiltration.exists_smoothGradedObject_subquotient` places `D` in
one actual smooth grade `t.smoothGradedObject j`. Its proof applies to an
arbitrary finite filtration: present the supplied occurrence as a
surjection from a subrepresentation to `D`, find consecutive steps at
which its restriction first becomes nonzero, and descend across the
kernel of the map into that grade. Irreducibility of `D` makes the
nonzero descended map surjective. It does not require simple grades or
finite length of the source.

Evaluate the supplied natural grade isomorphism at `(A,B)`. The underlying
representation of the smooth grade is definitionally the evaluated
quotient representation. The smooth piece forgets to the existing
`leibnizPiece` by definition. Thus `Representation.equivOfIso` gives the
actual representation equivalence between this smooth grade and the
selected smooth piece. `SmoothRep.mkIso` and
`SmoothRep.IsSubquotient.of_iso_right` transport the existing occurrence.
The required feasible index is `e.symm j`.

For the nonzero-factor refinement, the first private helper proves that
an actual ambient object containing an irreducible actual subquotient is
nontrivial. In an injective/surjective presentation through an object `X`,
a subsingleton ambient object forces `X` to be subsingleton by injectivity,
and then forces the irreducible target to be subsingleton by surjectivity.
This contradicts the nontriviality of a simple group-algebra module.
Apply this observation to the selected piece.

If either derivative factor had a subsingleton carrier, the published
`ProductVanishing.subsingleton_binary` would make their binary product
subsingleton. The second private helper eliminates the rank equality to
preserve this property through `generalLinearRankCast`. The result
contradicts nontriviality of the selected piece. The two negations of
subsingleton are converted to `Nontrivial`, and the same occurrence is
retained.

For the final corollary, apply
`generalLinearDerivativeExactness.{uF,max uF uV} F T ψ (a+b) d hd`.
`ExactSmoothTransport.map_isSubquotient` sends the actual occurrence of
`Q` in the source product to the corresponding occurrence between their
derivatives. `smoothSubquotientTransitivity` composes this with the given
occurrence of `D` in the derivative of `Q`. The nonzero-factor extraction
lemma then applies to the derivative of the original product. All objects
in this exactness argument use the same carrier universe `max uF uV`;
the original factors retain their independent universe `uV`.

## Provenance and published inputs

This is derived internal material. It composes published constructions
and elementary quotient, simple-module and equality-transport arguments;
it does not formalize an additional literature assertion. The general
Leibniz theorem is the published formalization of BZ77 Corollary 4.14(c)
with its arbitrary-carrier rank-zero extension. Its original-source
correspondence and normalization audit remain in
[GeneralLinearDerivativeLeibnizFiltrationProof](GeneralLinearDerivativeLeibnizFiltrationProof.md).
No segment derivative result from Zelevinsky 1980 is an input.

The five direct imports have the following precise roles.

| Module, after `Langlands.Representation.` | Used proved construction |
| --- | --- |
| `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | Unconditional all-rank actual Leibniz filtration, its full feasible indexing and natural grade isomorphisms |
| `Derivative.ProductVanishing` | A zero factor makes the actual binary product zero, including the tensor models at rank zero |
| `Filtration.ActualGradedExtraction` | Actual irreducible subquotient extraction from an arbitrary finite filtration |
| `Filtration.ExactSmoothSubquotients` | Preservation of the actual subquotient relation by a supplied exact functor |
| `Filtration.SubquotientAlgebraProof` | Transitivity of actual smooth subquotients |

The inherited exactness theorem is a proved composite of restriction,
rank transport, iterated normalized `Φ⁻` and normalized `Ψ⁻`. The last two
use independently proved general mirabolic-minus exactness. The actual
Leibniz proof assembles the two-orbit restriction sequence and the proved
general left and right mixed derivative comparisons by exact image
filtrations, reindexing and splicing. Its rank-zero cases use explicit
tensor/quotient maps, rather than a dimension-one assumption.

The generic extraction input uses only invariant subspaces, quotient
lifts and simple-module algebra. The exact-subquotient input maps an
actual injective/surjective presentation. The transitivity input pulls
back a subrepresentation along a surjection and composes actual quotient
maps. The private helpers added here use only the same presentation,
nontriviality of a simple module, and elimination of a rank equality.
These proof routes establish the dependency boundary as well as the
module-name audit below.

## Independence and scope audit

The host is task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`. The trusted
operator decisions
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md)
and
[30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
retain its full independence conditions. The first permits independently
proved general BZ77 derivative infrastructure; the second records further
permitted general infrastructure; the third permits a separately proved
support-only terminal-truncation statement, with explicit limits. This
module uses only general derivative theory and generic algebra. It
introduces no segment derivative or support statement and needs no
strengthening of that support-only permission.

| Excluded result or boundary | Verification for this module and its inherited closure |
| --- | --- |
| Ze80 §§3.5/9.6, their segment derivative formulas and proof successors | No segment derivative module occurs. The only derivative formulas used are the general BZ77 Leibniz and exactness results just described. |
| Full segment/head/socle Jacquet formulas and exponent norm formula, including tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | None occurs in the closure or supplies a proof dependency. General coinvariant exactness and elementary induction infrastructure do not use these conclusions. |
| The host product criterion in either direction and segment-socle product criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Neither conclusion, a successor nor a downstream consumer is imported or used. No linkage hypothesis appears. |
| Parent `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | No generic uniqueness or comparison of different products is used. |
| Multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | None supplies an input. Finite indexing here concerns feasible derivative orders only. |
| Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`, `SquareIntegrableLanglandsClassification` and task `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | No such module or conclusion is a direct or transitive dependency. |
| Segment-socle part of task `8e5b4563`, linked-pair structure, adjacent commutation and two-supercuspidal product criteria | None is imported or invoked. `ProductVanishing` uses general zero-object algebra; its proof of the lemma used here does not depend on its former two-supercuspidal consumer. |
| Classification-named imports | Exactly `ConstituentRelations`, `Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, `SupercuspidalSupport` and `SupercuspidalTwist` occur. They provide definitions, actual subquotient presentations and lower equivalence/twist infrastructure. No global support existence, support uniqueness or representation classification is invoked. |
| Whittaker irreducible/Levi/supercuspidal coinvariant finiteness and dependent mirabolic finite length | These conclusions and their proof routes are absent. General minus exactness and the conservative derivative-detection import use compact finite-orbit averaging and independent rank/Fourier arguments, not those finiteness results. |
| Actual representations, original universes and arbitrary rank-zero carriers | The smooth piece retains both actual derivatives, their product and the prescribed cast. Exact transport is at `max uF uV`; no resize of `A,B` or scalar replacement of a `GL_0` carrier occurs. |
| Pending work and user controls | No pending dual-head candidate, unpublished support proof or stronger segment derivative result is used. No ownership or run-control change is needed. |

This module does not prove the host irreducibility criterion. Simple
constituents of the factor derivatives, support aggregation and equality,
nonlinkage survival, and the linked converse remain separate obligations.

## Complete import inventory and validation

Recursive traversal at published Library commit
`545ccb3366b363dc0fe0a6d000b281a88d7c2407` finds 365 project modules,
including this new entry, and 145 named external import roots. All 364
inherited Lean/Markdown pairs are nonempty and byte-identical to that
Library tree. None is an unpublished dependency or an edited imported
pair. The inherited pairs also exactly match their corresponding pairs
in the earlier product-top-derivative dependency inventory; no new lower
branch is introduced.

After removing nested comments and string literals, a recursive code scan
finds no excluded name or inherited task-identifier match and no proof
hole, new axiom or prohibited execution syntax. The proof-route
inspection above supplements this scan; a name scan alone would not
establish independence. The private reproducibility inventory is
`.private/notes/worker357-leibniz-extraction-import-audit-2026-11-02.json`.
The complete module-name lists below make the inventory reconstructible
from the public imports without that private file.

Development check `50279aec-3cfc-422b-91ce-fa16dec08fbb`, in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, compiled the entry with zero errors
and warnings. Inspection of the final extraction corollary reports
independent level parameters `uF,uV` and only `propext`,
`Classical.choice` and `Quot.sound`. This is a development check;
independent semantic review and publication are still required.

The following grouped inventories use each prefix followed by its
immediate module suffixes; they expand to precisely the full names.

### Project modules

- `Langlands.Analysis.Local`: `CompactOpenCoverUnimodularityProof`, `CompactOpenCoverUnimodularityStatement`, `ModularCompactAverage`, `QuotientAutomorphismProof`, `QuotientAutomorphismStatement`, `QuotientAverageReal`, `QuotientAveragingKernel`, `QuotientComplex`, `QuotientFunctional`, `QuotientMass`, `QuotientMeasure`, `QuotientMeasureExistence`, `QuotientMeasureExistenceStatement`, `QuotientMeasurePrerequisites`, `QuotientPositiveLifting`, `QuotientTopology`, `QuotientTranslation`, `SplitKernelQuotient`.
- `Langlands.Group`: `HaarModulus`.
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
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeExactnessProof`, `GeneralLinearDerivativeExactnessStatement`, `GeneralLinearDerivativeLeibnizBoundary`, `GeneralLinearDerivativeLeibnizFiltrationProof`, `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeftMixedProductDerivativeProof`, `LeftMixedProductHigher`, `LeftMixedProductVanishing`, `LeftMixedProductZeroRank`, `LeibnizConstituentExtraction`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizPositiveGluing`, `LeibnizQuotientPiece`, `LeibnizRankZeroBoundary`, `LeibnizRankZeroGluing`, `LeibnizRestrictionCompat`, `LeibnizRestrictionExact`, `LeibnizZeroFirstPiece`, `LevelCalculus`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionProof`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicDeterminant`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusExactnessProof`, `MirabolicMinusExactnessStatement`, `MirabolicMixedOrbitCharacters`, `MirabolicPhiMinusMackey`, `MirabolicPlus`, `MirabolicProductMinusBoundary`, `MirabolicProductMinusCompatibilityStatement`, `MirabolicProductMinusLeftPhi`, `MirabolicProductMinusLeftPhiCoefficient`, `MirabolicProductMinusLeftPhiCompactComparison`, `MirabolicProductMinusLeftPhiHaar`, `MirabolicProductMinusLeftPhiHostTransport`, `MirabolicProductMinusLeftPhiIdentityComparison`, `MirabolicProductMinusLeftPhiInductionNormalization`, `MirabolicProductMinusLeftPhiLocalization`, `MirabolicProductMinusLeftPhiMackeyLocalization`, `MirabolicProductMinusLeftPhiNormalization`, `MirabolicProductMinusLeftPhiNormalizedSection`, `MirabolicProductMinusLeftPhiSection`, `MirabolicProductMinusLeftPhiSourceAction`, `MirabolicProductMinusLeftPhiSourceComparison`, `MirabolicProductMinusLeftPhiStagesComparison`, `MirabolicProductMinusLeftPsi`, `MirabolicProductMinusLeftPsiInduction`, `MirabolicProductMinusPhiKernelComparison`, `MirabolicProductMinusRightBoundary`, `MirabolicProductMinusRightPhi`, `MirabolicProductMinusRightPhiAssembly`, `MirabolicProductMinusRightPhiCycle`, `MirabolicProductMinusRightPhiCycleCoefficient`, `MirabolicProductMinusRightPhiCycleGroups`, `MirabolicProductMinusRightPhiIdentity`, `MirabolicProductMinusRightPhiIdentityCoefficient`, `MirabolicProductMinusRightPhiIdentityGroups`, `MirabolicProductMinusRightPsi`, `MirabolicProductMinusRightPsiCoefficient`, `MirabolicProductMinusRightPsiGroups`, `MirabolicProductMinusRightPsiZero`, `MirabolicProductRestriction`, `MirabolicProductRestrictionCasts`, `MirabolicProductRestrictionFactors`, `MirabolicProductRestrictionMackey`, `MirabolicProductRestrictionOrbits`, `MirabolicProductRestrictionStabilizers`, `MirabolicProductRestrictionStatement`, `MirabolicProductRestrictionTransport`, `MixedProductDerivativeStatement`, `MixedProductRankCast`, `OrderRecursion`, `ProductVanishing`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationProof`, `RightMixedProductDerivativeFiltrationStatement`, `RightMixedProductDerivativePositive`, `RightMixedProductZeroRank`, `ShortExactFunctorLaws`, `ZeroRankTensor`.
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
- `Langlands.Representation.Tensor`: `ExternalFiltration`, `ExternalSubrepresentation`, `Filtration`, `Finite`, `FiniteEquivalences`, `FiniteFiltration`, `OneFactor`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Unitary`: `Basic`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`, `Iwasawa`.
- `Langlands.Topology`: `CompactNormCharacter`.
- `Langlands.Topology.CompactOpen`: `ConjugationStabilizer`, `NeighborhoodBasis`, `NeighborhoodBasisStatement`.
- `Langlands.Topology.Nonarchimedean`: `Subgroup`.
- `Langlands.Weil.Representation`: `Basic`, `Determinant`, `IsomorphismInvarianceProof`, `Operations`.

### External import roots

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
