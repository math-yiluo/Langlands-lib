# Proof of the mirabolic support shift for cuspidal products

The module has two helper modules,
`Classification.CuspidalProductContragredient` and
`Classification.MirabolicDerivativeContragredient`. The quotient form of
BZ77 Lemma 4.7(a) is imported from the published helper
`Classification.CuspidalProductDerivativeQuotientSupport`.

This module proves the published proposition
`Langlands.Classification.CuspidalProductMirabolicSupportShift.{uF,uV} F T`
(module `Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement`).
This is Bernstein–Zelevinsky 1977, Lemma 4.7(b), in its mirabolic form.

## The theorem

```lean
theorem Langlands.Classification.cuspidalProductMirabolicSupportShift
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    CuspidalProductMirabolicSupportShift.{uF, uV} F T
```

The universes `uF` (field) and `uV` (supercuspidal carriers) are independent,
and there is no other premise. The statement is unchanged. Take any nontrivial
unitary additive character `ψ`, any `N r`, and cuspidal data
`ρ : Fin r → T.CuspidalDatum` with `∑ (ρ i).rank = N + 1`. Take any family `A`
of actual supercuspidal representatives, and any `W` with an injective
intertwiner `f : W → π|P`, where `π = A_1 × ⋯ × A_r =
T.cuspidalProductInduced ρ h A` and `P = P_(N+1)`. Take any `k` with
`0 < k ≤ N + 1` and `level W = k`, any irreducible subrepresentation `σ` of
`W^(k)`, and any supercuspidal support `s` of `σ`. Then the multiset
`s.map (twist 1)` (that is, `ν · s`) is a submultiset of `ρ_1 + ⋯ + ρ_r`.
Nothing is assumed of `W` beyond the injective intertwiner. The `ρ_i` are
arbitrary: any order, repetitions, linked or not.

## The proof

Write `ν = |det|`, `π̄ = ν π̃` and `ρ̄_i = ν ρ̃_i`. The final theorem
introduces the data and splits into two cases: `k < N + 1` and `k = N + 1`.

### Case `k = N + 1`

Then `σ` is a representation of `GL_0`. Lemma
`eq_zero_of_isSupercuspidalSupport` shows that every supercuspidal support of
a representation of `GL_0` is empty. A support `ofFn ρ'` of `σ` has
`∑ (ρ' i).rank = 0`, and every rank is positive, so `ρ'` has no index. Hence
`s = 0`, and `s.map (twist 1) = 0 ≤ ofFn ρ`.

### Case `0 < k < N + 1`

This case installs the supplied topologies: `T.topology`, and
`T.generalLinearTopologicalGroup` for `N + 1` and `N + 1 - k`.

1. **Product of the twisted duals** (BZ77 §2.3(d), §1.9(f); source steps 1
   and 2). Put `ρ̄ = twistedDualData 1 ρ`, the data `i ↦ ν ρ̃_i`. Its actual
   representatives are `Ā_i = twistedDualRep T 1 (A i) = |det|^1 Ã_i`, which
   are supercuspidal and represent `ρ̄_i` (`twistedDualRep_represents`). The
   ranks are unchanged, so the same `h` is the rank sum for `ρ̄`. The helper
   `nonempty_twistedDual_cuspidalProductEquiv 1 ρ h A` gives a linear
   equivalence of representations
   `Φ : Ā_1 × ⋯ × Ā_r ≃ |det|^1 ⊗ (A_1 × ⋯ × A_r)~`. Put
   `π' = T.cuspidalProductInduced ρ̄ h Ā`, so `π' ≅ π̄`.
2. **Pairing of `W` with `π'|P`** (source step 3). The helper
   `exists_determinant_pairing π π' Φ W f hf` gives a bilinear form `β` on
   `W × π'|P` with `β (W g w) (π' g y) = |det g| · β w y` for `g ∈ P`. The
   form is nondegenerate in `W`. Explicitly, `β w y = ⟨Φ y, f w⟩`: the
   natural pairing of `π` and `π̃`, transported along `Φ`.
3. **Pairing of derivatives and the map to `σ̃`** (source steps 4 and 5). The
   helper `exists_derivative_hom_contragredient ψ π' W β hβ k hk hlevel σ hσ`
   applies the published BZ77 Proposition 3.8
   (`Derivative.mirabolicHighestDerivativePairing`) to `W`, `π'|P` and `β`.
   Since `k > 0` is the level of `W`, this gives an invariant pairing of
   `W^(k)` and `(π'|P)^(k)`, nondegenerate in `W^(k)`. Restricting it to
   `σ ⊆ W^(k)` gives a morphism
   `q : (generalLinearDerivative T ψ (N + 1) k hk.2).obj π' ⟶ σ̃` with
   `SmoothRep.hom q ≠ 0`. The `GL` derivative of `π'` is, as an object, the
   mirabolic derivative of `π'|P` (helper
   `mirabolicDerivativeOfOrder_restriction`).
4. **`σ̃` is irreducible.** `σ` is irreducible, hence admissible: this is the
   first component of the published `CuspidalSupport.cuspidalEmbedding`. The
   published `SmoothRep.isIrreducible_contragredient_iff`, with the cofinal
   compact open subgroups `compactOpen_cofinal F T (N + 1 - k)`, then shows
   that `σ̃` is irreducible.
5. **Support of `σ̃`.** By the helper `isSupercuspidalSupport_contragredient hs`,
   `s̃ = s.map dualDatum` is a supercuspidal support of `σ̃`.
6. **Lemma 4.7(a) for `π'`, quotient form** (source step 6). The local lemma
   `le_of_derivative_hom` applies to `ρ̄`, `Ā`, `τ = σ̃` and `q`. It says: if
   `0 < k < n`, and an irreducible `τ` receives a nonzero morphism from the
   order-`k` `GL` derivative of a cuspidal product `ρ̄_1 × ⋯ × ρ̄_r` of rank
   `n`, then every supercuspidal support of `τ` is a submultiset of
   `ρ̄_1 + ⋯ + ρ̄_r`. Its proof calls
   `CuspidalProductDerivativeQuotientSupport.derivative_quotient_support`.
   That theorem takes the underlying linear map of `q`, its nonvanishing and
   its `GL_(n-k)`-equivariance. It returns data `ρ''` with
   `T.IsCuspidalConstituent ρ'' τ` (so `ofFn ρ''` is a support of `τ`) and
   `ofFn ρ'' ≤ ofFn ρ̄`. The published support uniqueness
   `glSupercuspidalSupportUniqueness`, at rank `n - k > 0`, identifies the
   given support with `ofFn ρ''`. So `s̃ ≤ ν ρ̃_1 + ⋯ + ν ρ̃_r`.
7. **Undo the dual and the twist.** The helper `twist_le_of_dual_le ρ s`
   turns `s.map dualDatum ≤ ofFn (twistedDualData 1 ρ)` into
   `s.map (twist 1) ≤ ofFn ρ`. It applies `x ↦ ν x̃` to both sides. On the
   left, `ν (x̃)~ = ν x` by `dualDatum_dualDatum`. On the right the map is an
   involution: `ν (ν x̃)~ = ν ν⁻¹ x = x`, by `dualDatum_twist`,
   `dualDatum_dualDatum` and `CuspidalDatum.twist_twist`.

Multiplicities are kept throughout: every inclusion is `≤` of multisets. The
final theorem has no hypothesis beyond the target's binders, and
the axiom check reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Relation to the source proof

BZ77 §4.8, printed pp. 455–456, proves (b) in six steps. Steps 1–4 are implemented as in the source. There are two
changes.

- **Step 5.** The source says that, since there is a nonzero pairing of `σ`
  and `π̄^(k)`, `σ̃ ∈ JH(π̄^(k))`. Here the pairing is turned into a nonzero
  morphism `π̄^(k) → σ̃` instead. So `σ̃` is an irreducible quotient of
  `π̄^(k)`. No Jordan–Hölder series and no finite length of `π̄^(k)` is used.
- **Step 6.** The source proves Lemma 4.7(a) from §4.4 and Corollary 4.6, that
  is, from derivatives of cuspidal representations and the Leibniz filtration
  of the derivatives of a product. This proof uses neither the Leibniz
  filtration nor the exactness of derivatives; it uses the quotient form
  of 4.7(a) proved in the published helper
  `Classification.CuspidalProductDerivativeQuotientSupport`. Its route is as
  follows. The published Ze80 Proposition 3.7(b)
  (`Derivative.partialDerivativeJacquetComparison`) identifies the derivative
  with a partial derivative of a two-block Jacquet module. The published
  geometric lemma (`Geometric.padicGeometricLemma`, BZ77 §§2.11–2.12) filters
  that Jacquet module of the cuspidal product. Pieces with a proper source
  refinement vanish by cuspidality. A whole-source piece is induced from a
  transported cuspidal representation. Its Levi factorization and the
  published association of cuspidal data give a support bounded by `ρ`. The
  helper uses neither the Leibniz filtration nor §4.4. Support uniqueness
  (Ze80 1.10, published) converts its constructed support into the bound for
  every support.

The other ingredients of the source are proved in the helper modules:

- the contragredient and twist of a product of cuspidal representations, for
  every `r` and all ranks (`Classification.CuspidalProductContragredient`);
- the support of a contragredient;
- the passage from the pairing to the map `π̄^(k) → σ̃`
  (`Classification.MirabolicDerivativeContragredient`).

## Normalizations

- **Product.** `T.cuspidalProductInduced ρ h A` is the published normalized
  parabolic induction from the standard upper block parabolic of shape
  `((ρ 1).rank, …, (ρ r).rank)` (`Classification.SupercuspidalSupport`).
  `Classification.CuspidalProductContragredient` identifies the contragredient
  of the product with the product of the contragredients. It also identifies
  `|det|^1 ⊗ −` of the product with the product of the twists. Both hold for
  every `r` and all ranks, with the Library's normalization.
- **Twist.** `ν = |det| = T.determinantNorm`, and
  `T.determinantPowerCharacter n t = |det|^t`. On cuspidal data,
  `CuspidalDatum.twist t` is the published class-level twist by `|det|^t`
  (`Classification.Segments`). `dualDatum` is the class of the contragredient
  (helper 1).
- **Derivatives.** The proof uses the Library's determinant-normalized
  `mirabolicDerivativeOfOrder` (`Derivative.Homogeneity`) and
  `generalLinearDerivative` (`Derivative.Iteration`), unchanged, with the same
  `ψ` throughout. `derivative_quotient_support` is stated for the same
  `generalLinearDerivative`. Its normalization enters only through the
  published Ze80 3.7(b) comparison for these functors.
- **Pairing.** In the source's convention, the natural pairing of `π` and
  `ν π̃` is a `ν⁻¹`-pairing: BZ77 §3.6, printed p. 452, writes
  `χ(g) B(gξ, gη) = B(ξ, η)`. The Library convention is
  `InvariantBilinear.forms ρ σ χ`: `B (ρ g v) (σ g w) = χ g * B v w`. In it
  the pairing has covariance `g ↦ |det g|`, which is exactly the hypothesis of
  the published `MirabolicHighestDerivativePairingStatement`. The Haar-modulus
  comparison is not used.

## Universes

`p`, `F : PadicField.{uF} p` and `T` are arbitrary. Cuspidal data have
carriers in `uV`. All representations of `GL_(N+1)`, of `P_(N+1)` and of
`GL_(N+1-k)` (`π`, `π'`, `W`, `σ`, `σ̃`) have carriers in `max uF uV`, the
carrier universe of the published cuspidal product. The helpers are applied
at these universes: `derivative_quotient_support.{uF, uV}` and
`glSupercuspidalSupportUniqueness.{uV, uF}`.

## Use of the 4.7(a) helper

`Classification.CuspidalProductDerivativeQuotientSupport` was written for the
proof of `HighestDerivativeSupportShift`, whose other modules this proof
excludes. Its integration (commit `368b3cec32d30129c07825e0ce549058b99762f4`)
also moved two published transport theorems into the shared module
`CuspidalSupport.WholeLeviTransport`. Both modules are imported here, since
their proof dependencies avoid every exclusion. The other exclusions stand,
including `HighestDerivativeSupportShift` and
`HighestDerivativeSupportShiftBoundary`.

The audit below covers the whole closure, including these two modules. No
other module or proof of `HighestDerivativeSupportShift` is imported.

## Direct imports and the proved results used

| Import | Results used |
| --- | --- |
| `Classification.CuspidalProductContragredient` | `twistedDualData`, `twistedDualRep`, `twistedDualRep_represents`, `nonempty_twistedDual_cuspidalProductEquiv`, `isSupercuspidalSupport_contragredient`, `twist_le_of_dual_le` |
| `Classification.MirabolicDerivativeContragredient` | `exists_determinant_pairing`, `exists_derivative_hom_contragredient` (through `Derivative.mirabolicHighestDerivativePairing`) |
| `Classification.CuspidalProductDerivativeQuotientSupport` | `derivative_quotient_support` |
| `Classification.SupercuspidalSupportUniquenessProof` | `glSupercuspidalSupportUniqueness` |
| `Classification.CuspidalProductMirabolicSupportShiftStatement` | the target proposition only |

The helper modules also bring in these published results:

- `CuspidalSupport.cuspidalEmbedding` (`CuspidalSupport.CuspidalEmbeddingProof`),
  used for admissibility of `σ`;
- `SmoothRep.isIrreducible_contragredient_iff` and `compactOpen_cofinal`
  (`Category.Contragredient`).

The published inputs of the two helpers are listed in their own Markdown.
They are general smooth duality, the contragredient of supercuspidal
representations (BZ77 §2.4(c), `Classification.SupercuspidalContragredientProof`),
induction and twists, exactness of the smooth contragredient, and the BZ77 3.8
pairing proof. The published inputs of `derivative_quotient_support` are
listed in its Markdown table: the geometric lemma, cuspidal Jacquet vanishing,
Levi factorization and association of cuspidal data, refined induction of
tensors, and the Ze80 3.7(b) comparison. `CuspidalSupport.WholeLeviTransport`
imports only `CuspidalSupport.MinimalConjugatingCosetsProof`,
`CuspidalSupport.AssociationReduction` and
`CuspidalSupport.MinimalWeylTransportProof`.

## Complete import closure

Computed by following every `import Langlands.…` line from this module at
Library commit `b22e185743f7c318f709e14e422801f4360105d5`, together with the
two helper modules. Every Library file in the closure is
byte-identical to that commit. Besides this module, the closure has 603
project modules. They are listed below by namespace, with prefix
`Langlands.Representation.X` or `Langlands.X` shown once per line. Mathlib is
not listed.

- `Langlands.Algebra` (8): `CommutingDimensionHelpers`, `CommutingDimensionNilpotent`, `CommutingDimensionNumerics`, `CommutingDimensionPrimary`, `CommutingDimensionRecurrence`, `SandwichDimensionBoundProof`, `SandwichDimensionBoundStatement`, `SeparatedMatrixRepresentations`
- `Langlands.Analysis` (18): `Local.CompactOpenCoverUnimodularityProof`, `Local.CompactOpenCoverUnimodularityStatement`, `Local.ModularCompactAverage`, `Local.QuotientAutomorphismProof`, `Local.QuotientAutomorphismStatement`, `Local.QuotientAverageReal`, `Local.QuotientAveragingKernel`, `Local.QuotientComplex`, `Local.QuotientFunctional`, `Local.QuotientMass`, `Local.QuotientMeasure`, `Local.QuotientMeasureExistence`, `Local.QuotientMeasureExistenceStatement`, `Local.QuotientMeasurePrerequisites`, `Local.QuotientPositiveLifting`, `Local.QuotientTopology`, `Local.QuotientTranslation`, `Local.SplitKernelQuotient`
- `Langlands.Group` (53): `GL.Basic`, `GL.BlockContractionProof`, `GL.BlockContractionStatement`, `GL.BlockIwahoriBasis`, `GL.BlockIwahoriBasisStatement`, `GL.BlockIwahoriDefinitions`, `GL.BlockModulus`, `GL.BlockModulusHaarProof`, `GL.BlockModulusHaarStatement`, `GL.BlockUnipotentCoordinates`, `GL.BlockUnipotentHaarProof`, `GL.BlockUnipotentHaarStatement`, `GL.Blocks`, `GL.CartanProof`, `GL.CartanStatement`, `GL.CompactOpen`, `GL.CountabilityProof`, `GL.CountabilityStatement`, `GL.DominantExponentGeneration`, `GL.IntegralSubgroup`, `GL.InverseTransposeIwahoriProof`, `GL.InverseTransposeIwahoriStatement`, `GL.Maps`, `GL.Mirabolic`, `GL.MirabolicProjection`, `GL.MirabolicRadical`, `GL.Nonarchimedean`, `GL.NonarchimedeanStatement`, `GL.NormalizedCharacter`, `GL.OneBlockShape`, `GL.OppositeBlocks`, `GL.Padic`, `GL.PadicBlocks`, `GL.PadicOppositeBlocks`, `GL.PadicUpperUnipotent`, `GL.ParabolicModularCharacter`, `GL.PrincipalBlockFactorizationProof`, `GL.PrincipalBlockFactorizationStatement`, `GL.PrincipalLevelDominance`, `GL.RankMaps`, `GL.RefinementCoordinates`, `GL.ReverseBlocks`, `GL.SingleBlock`, `GL.SingletonBlocks`, `GL.Transvection`, `GL.TriangularParabolic`, `GL.UpperBruhatEmbedding`, `GL.UpperBruhatPivotProof`, `GL.UpperBruhatPivotStatement`, `GL.UpperBruhatProof`, `GL.UpperBruhatStatement`, `GL.UpperUnipotent`, `HaarModulus`
- `Langlands.HarmonicAnalysis` (16): `AlgebraicIntegral`, `AlgebraicIntegrand`, `Basic`, `CharacterTransport`, `Conductor`, `FiniteProductMeasureScaling`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`, `RowSchwartzAction`, `RowTestSmoothProof`, `RowTestSmoothStatement`, `TriangularTranslationProof`, `TriangularTranslationStatement`
- `Langlands.LocalFactor` (3): `Euler`, `Euler.Definitions`, `Harmonic.Statement`
- `Langlands.LocalField` (6): `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology`
- `Langlands.Representation.Category` (5): `Basic`, `ClassInvariants`, `Contragredient`, `Subquotients`, `Twist`
- `Langlands.Representation.Classification` (16): `ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`, `CuspidalProductContragredient`, `CuspidalProductDerivativeQuotientSupport`, `CuspidalProductMirabolicSupportShiftStatement`, `MirabolicDerivativeContragredient`, `Segments`, `Supercuspidal`, `SupercuspidalContragredient`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientProof`, `SupercuspidalContragredientStatement`, `SupercuspidalSupport`, `SupercuspidalSupportStatement`, `SupercuspidalSupportUniquenessProof`, `SupercuspidalTwist`
- `Langlands.Representation.Compact` (7): `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`, `SurjectivityProof`, `SurjectivityStatement`
- `Langlands.Representation.CompactCoefficient` (17): `AdmissibleComplement`, `AdmissibleLifting`, `AdmissibleRetraction`, `AmbientProjector`, `Classes`, `ConditionalProjection`, `FixedLevelFiniteness`, `FixedVectorsFiniteDimensional`, `GroupTransport`, `Isotypic`, `IsotypicTransport`, `NormalSubgroupDecomposition`, `OrthogonalProjectorFamily`, `SemisimplicityProof`, `SemisimplicityStatement`, `TotalCompactness`, `TotalProjector`
- `Langlands.Representation.Conductor` (5): `Congruence`, `Definitions`, `PrincipalCongruence`, `PrincipalCongruenceBasisProof`, `PrincipalCongruenceBasisStatement`
- `Langlands.Representation.CuspidalSupport` (78): `AssociatedAssembly`, `AssociatedConditional`, `AssociatedGeometricPieceVanishingProof`, `AssociatedGeometricPiecesEquivalenceProof`, `AssociatedGeometricPiecesProof`, `AssociatedGeometricPiecesStatement`, `AssociatedProof`, `AssociatedRankZero`, `AssociationForwardStatement`, `AssociationLawsProof`, `AssociationLawsStatement`, `AssociationReduction`, `AssociationReverseProof`, `AssociationReverseStatement`, `BlockMap`, `BlockPermutation`, `CompactCoefficientFinitenessProof`, `CompactCoefficientFinitenessReduction`, `CompactCoefficientFinitenessStatement`, `CuspidalEmbeddingProof`, `CuspidalTensorAssociationProof`, `CuspidalTensorProof`, `CuspidalTensorStatement`, `CuspidalityComparisonProof`, `CuspidalityComparisonStatement`, `DeterminantUnit`, `DeterminantUnitCartanSupport`, `DeterminantUnitCornerStructureProof`, `DeterminantUnitCornerStructureStatement`, `DualAveraging`, `FiltrationQuasicuspidality`, `GroupTransport`, `HarishChandraAssembly`, `HarishChandraBoundaryProof`, `HarishChandraBoundaryStatement`, `HarishChandraConverseProof`, `HarishChandraConverseStatement`, `HarishChandraForwardProof`, `HarishChandraStatement`, `JacquetInductionStatement`, `JacquetSubquotientProof`, `JacquetSubquotientStatement`, `JacquetVanishingHelpers`, `JacquetVanishingSmoothPieces`, `JacquetVanishingSubgroups`, `LeviAdmissibleFactorizationProof`, `LeviAdmissibleFactorizationStatement`, `LeviAssociation`, `LeviCompactPart`, `LeviDecompositionAssembly`, `LeviDefinitions`, `LeviGapVanishing`, `LeviQuasicuspidalDecompositionProof`, `LeviSplitContraction`, `LeviTensorFactorizationProof`, `LeviTensorFactorizationStatement`, `LeviTensorReflectionProof`, `LeviTensorReflectionStatement`, `MinimalConjugatingCosetsProof`, `MinimalJacquetProof`, `MinimalJacquetStatement`, `MinimalWeylTransportProof`, `NaturalProjectorDecomposition`, `NonassociatedJacquetSubquotientsProof`, `NormalizedCuspidalInductionStatement`, `PointwiseProjectorSum`, `ProperInductionMaps`, `ProperInductionProof`, `ProperInductionStatement`, `QuasicuspidalEmbeddingProof`, `QuasicuspidalLeviAdmissibilityProof`, `QuasicuspidalPrerequisitesStatement`, `QuasicuspidalStructureStatement`, `StandardJacquetComparisonProof`, `TotalConjugatingCountProof`, `TotalConjugatingCountStatement`, `WholeLeviTransport`, `ZeroRankEmbeddingProof`
- `Langlands.Representation.Derivative` (24): `Homogeneity`, `Iteration`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`, `MirabolicHighestDerivativePairingStatement`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusPairingTransferProof`, `MirabolicMinusPairingTransferStatement`, `MirabolicPhiMinusNondegeneratePairing`, `Partial`, `PartialDerivativeJacquetComparisonProof`, `PartialDerivativeJacquetComparisonStatement`, `PartialDerivativeJacquetLHS`, `PartialDerivativeJacquetNormalization`, `PartialDerivativeJacquetRHS`, `PartialDerivativeJacquetRHSComparison`, `PartialLocalizationCharacter`, `PartialLocalizationData`, `TopLocalizationData`
- `Langlands.Representation.Dual` (1): `Definitions`
- `Langlands.Representation.Filtration` (23): `CoinvariantVanishingStatement`, `CommonSubquotientStatement`, `Definitions`, `InvariantBilinear`, `InvariantBilinearBounds`, `IsoTransport`, `LengthCriterionProof`, `LengthCriterionStatement`, `MultiplicityStatement`, `NonzeroHomCommonSubquotientProof`, `NonzeroHomCommonSubquotientStatement`, `ObjectDefinitions`, `QuasicuspidalVanishingProof`, `QuotientFirstIso`, `SimpleSubquotientFactorProof`, `SimpleSubquotientFactorStatement`, `SubquotientAlgebraProof`, `SubquotientAlgebraStatement`, `SubsingletonProof`, `Transport`, `VanishingStatement`, `ZeroFactorDeletionProof`, `ZeroFactorDeletionStatement`
- `Langlands.Representation.Geometric` (72): `BlockIntersectionSplitting`, `BlockSixDecomposableProof`, `BlockSixDecomposableStatement`, `BruhatDescent`, `BruhatMatrixExistenceProof`, `BruhatMatrixStatement`, `BruhatWeylReflectionProof`, `ClosedSubgroupAssembly`, `ClosedSubgroupDefinitions`, `ClosedSubgroupMackeyProof`, `ClosedSubgroupStatement`, `CompactOrbitRestriction`, `CompactSmoothComparison`, `ConditionalAssembly`, `CorrectionSubgroupCoordinates`, `CorrectionSubgroupDiagonalHaarProof`, `CorrectionSubgroupDiagonalHaarStatement`, `CosetAction`, `CosetOrbitHomeomorph`, `CosetOrbitOrdering`, `FlattenedLevi`, `GeneralCorrectionCharacters`, `GeneralIntersectionNormalizers`, `GeneralIntersections`, `GeometricLemmaProof`, `GeometricLemmaStatement`, `IntersectionLeviDiagonalCharacterProof`, `IntersectionLeviDiagonalCharacterStatement`, `IntersectionLeviModulusBalance`, `IntersectionTransport`, `MonotoneBlocksProof`, `MonotoneBlocksStatement`, `OrbitRepresentatives`, `OrbitRestriction`, `OrbitSectionExtensionProof`, `OrbitSectionExtensionStatement`, `PadicCorrectionCancellationProof`, `PadicCorrectionCancellationStatement`, `PadicParabolicBruhatProof`, `ParabolicOrbitCoefficientComparison`, `ParabolicOrbitCompactComparison`, `ParabolicOrbitComparisonData`, `ParabolicOrbitHaarComparison`, `ParabolicOrbitHaarRatio`, `ParabolicOrbitHaarTransport`, `ParabolicOrbitInductionTransport`, `ParabolicOrbitJacquet`, `ParabolicOrbitJacquetProof`, `ParabolicOrbitJacquetStatement`, `ParabolicOrbitMeasureData`, `ParabolicOrbitNestedAction`, `ParabolicOrbitNormalization`, `ParabolicOrbitNormalizedCoefficient`, `ParabolicOrbitSectionComparison`, `ParabolicOrbitStagesCoefficient`, `ParabolicSupportFiltration`, `ParabolicSupportGradedProof`, `ParabolicSupportGradedStatement`, `ParabolicSupportJacquetProof`, `ParabolicSupportJacquetStatement`, `ParabolicSupportTransport`, `RefinedPositiveCharacter`, `RefinementDefinitions`, `RefinementFunctors`, `RefinementUniqueness`, `SmoothSupportFiltration`, `StandardIntersectionsProof`, `WeylDefinitions`, `WeylMinimalRepresentativeProof`, `WeylStatement`, `WeylUniquenessProof`, `WeylUniquenessStatement`
- `Langlands.Representation.Hecke` (13): `ActionIntegrand`, `ActionProjection`, `CommonInvarianceProof`, `CommonInvarianceStatement`, `Convolution`, `Corner`, `CornerAction`, `DoubleCoset`, `DoubleCosetSandwich`, `IntegratedAction`, `IntegratedConvolution`, `NormalizedIndicator`, `TestFunction`
- `Langlands.Representation.Induction` (52): `BlockCharacterAbsorption`, `BlockEquivalence`, `BlockFactors`, `CharacterTwistProof`, `CompactAutomorphism`, `CompactAutomorphismIntegralProof`, `CompactAutomorphismIntegralStatement`, `CompactBilinearPairing`, `CompactCoinvariantBijectivityProof`, `CompactCoinvariantBijectivityStatement`, `CompactCoinvariantIntegral`, `CompactCoinvariantLocalInverseProof`, `CompactCoinvariantLocalInverseStatement`, `CompactLocalSection`, `CompactLocalSectionSpanningProof`, `CompactLocalSectionSpanningStatement`, `CompactLocallyConstant`, `CompactPairingDuality`, `CompactQuotientCutoff`, `CompactQuotientProof`, `CompactScalarProof`, `CompactScalarStatement`, `CompactSurjectivityProof`, `CompactSurjectivityStatement`, `CompactTransitivityProof`, `CompactTransitivityStatement`, `Definitions`, `Equivalences`, `FiniteProductTensor`, `FiniteProductTensorBijectiveProof`, `FiniteProductTensorBijectiveStatement`, `InverseTranspose`, `NormalCoinvariantKernelProof`, `NormalCoinvariantKernelStatement`, `NormalCoinvariantMap`, `NormalCoinvariantProof`, `NormalCoinvariantStatement`, `NormalSplitComparison`, `OppositeParabolic`, `Parabolic`, `PiScalarIntegral`, `SplitKernelCompact`, `SplitKernelCovariance`, `SplitKernelEquivariant`, `SplitKernelIntegral`, `SplitQuotientProof`, `SplitQuotientStatement`, `SplitStagesComparison`, `SplitStagesRetraction`, `StructuralStatement`, `SurjectivityProof`, `SurjectivityStatement`
- `Langlands.Representation.Jacquet` (36): `BlockCompressionProof`, `BlockCompressionStatement`, `BlockPowerKernelProof`, `CanonicalLiftBijectivityProof`, `CanonicalLiftDefinitions`, `CanonicalLiftGroupTransportProof`, `CanonicalLiftGroupTransportStatement`, `CanonicalLiftIntertwinerNaturalityProof`, `CanonicalLiftIntertwinerNaturalityStatement`, `CanonicalLiftStatement`, `CharacterAveraging`, `CharacterTwistEquiv`, `Coinvariants`, `CompactCompressionStableDualityProof`, `CompactCompressionStableDualityStatement`, `CompressionStabilizationProof`, `CompressionStabilizationStatement`, `ExactProof`, `ExactStatement`, `Localization`, `LocalizationTower`, `LocalizationTransport`, `Normalized`, `OppositeCanonicalLiftProof`, `OppositeCanonicalLiftStatement`, `Parabolic`, `PositiveCharacter`, `RefinedOppositeCanonicalLiftProof`, `RefinedOppositeCanonicalLiftStatement`, `RefinedOppositeCompressionProof`, `RefinedOppositeCompressionStatement`, `RefinedOppositePowerKernelProof`, `RefinedOppositeStableImageProof`, `RefinedUpperCanonicalLiftProof`, `SmoothTwist`, `StablePairingProof`
- `Langlands.Representation.MatrixCoefficient` (3): `Definitions`, `LawsProof`, `LawsStatement`
- `Langlands.Representation` (2): `OrbitSpan`, `SubrepresentationLattice`
- `Langlands.Representation.Parabolic` (26): `AdmissibilityStatement`, `FlattenedRefinementModulusCalculation`, `GeometricPrerequisitesStatement`, `LeviBridges`, `LeviInflationAdmissibilityProof`, `NaturalInductionDualityFromScalar`, `NaturalInductionDualityProof`, `NaturalInductionDualityStatement`, `NaturalJacquetDualityProof`, `NaturalJacquetDualityStatement`, `NormalizedAdmissibilityProof`, `NormalizedInductionStatement`, `NormalizedJacquetExactnessProof`, `NormalizedJacquetStatement`, `OppositeRefinementDefinitions`, `OppositeRefinementFunctors`, `QuotientCompactProof`, `RefinedInductionAdmissibility`, `RefinedInductionTensorMap`, `RefinedInductionTensorNormalization`, `RefinedInductionTensorProof`, `RefinedInductionTensorStatement`, `RefinementCharacter`, `RefinementComposition`, `RefinementPreimage`, `UnipotentFiniteContainment`
- `Langlands.Representation.RankinSelberg` (21): `AnalyticStatement`, `EqualRankFrobeniusProof`, `EqualRankFrobeniusStatement`, `EqualRankTrilinearAssembly`, `EqualRankTrilinearReduction`, `EqualRankTrilinearUniquenessStatement`, `GeneralLinearUnimodularity`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `LocalFactor`, `Measures`, `QuotientIntegrals`, `RankOneQuotient`, `RationalContinuation`, `RationalZeta`, `TwistInvariance`, `UnimodularityStatement`, `UnipotentQuotient`, `UnipotentUnimodularity`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`
- `Langlands.Representation.Schur` (2): `CountableDimensionProof`, `CountableDimensionStatement`
- `Langlands.Representation.Shahidi` (1): `TwoBlocks`
- `Langlands.Representation.Smooth` (42): `Admissibility.CofinalProof`, `Admissibility.CofinalStatement`, `Admissibility.EmbeddingProof`, `Admissibility.EmbeddingStatement`, `Admissibility.EquivalenceProof`, `Admissibility.EquivalenceStatement`, `Contragredient.AdmissibleDualityProof`, `Contragredient.AdmissibleDualityStatement`, `Contragredient.CompactDualityProof`, `Contragredient.CompactDualityStatement`, `Contragredient.Definitions`, `Contragredient.ExactProof`, `Contragredient.ExactStatement`, `Contragredient.FixedVectorsDefinitions`, `Contragredient.HomDualityProof`, `Contragredient.HomDualityStatement`, `Contragredient.InvariantPairingProof`, `Contragredient.InvariantPairingStatement`, `Contragredient.LawsProof`, `Contragredient.LawsStatement`, `Definitions`, `Factorization.MultiplicityDefinitions`, `Factorization.TwoFactorExistenceProof`, `Factorization.TwoFactorStatement`, `FixedVectors.Definitions`, `FixedVectors.LawsProof`, `FixedVectors.LawsStatement`, `FixedVectors.OrderProof`, `FixedVectors.OrderStatement`, `Schur.Proof`, `Schur.Statement`, `SmallRealizationProof`, `SmallRealizationStatement`, `SmoothPart.BasicProof`, `SmoothPart.BasicStatement`, `SmoothPart.Definitions`, `SmoothPart.FixedVectorsDefinitions`, `Transfer.GroupEquivalence`, `Transfer.PullbackProof`, `Transfer.PullbackStatement`, `Transfer.SubquotientProof`, `Transfer.SubquotientStatement`
- `Langlands.Representation.Tensor` (12): `CoinvariantReflection`, `Finite`, `FiniteEquivalences`, `FiniteProperties`, `FiniteRegrouping`, `FlattenedGLRefinement`, `GLRefinement`, `SmoothDual`, `SmoothDualInjectivityProof`, `SmoothDualInjectivityStatement`, `SmoothDualSurjectivityProof`, `SmoothDualSurjectivityStatement`
- `Langlands.Representation.Twist` (16): `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `DualProof`, `DualStatement`, `RealPower`, `SmoothPartDefinitions`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`
- `Langlands.Representation.Unitary` (1): `Basic`
- `Langlands.Representation.Whittaker` (11): `Algebraic`, `AlgebraicTwist`, `CharacterChange`, `DualTransform`, `EntrywiseCharacter`, `GeneralLinear`, `Iwasawa`, `MirabolicQuotientMeasure`, `PrerequisiteInterfaces`, `PrerequisitesStatement`, `Twist`
- `Langlands.Topology` (7): `CompactNormCharacter`, `CompactOpen.ConjugationStabilizer`, `CompactOpen.NeighborhoodBasis`, `CompactOpen.NeighborhoodBasisStatement`, `GroupAction.FiniteOrbitProof`, `GroupAction.FiniteOrbitStatement`, `Nonarchimedean.Subgroup`
- `Langlands.Weil` (6): `Representation.Basic`, `Representation.Continuity`, `Representation.ContinuityProof`, `Representation.Determinant`, `Representation.IsomorphismInvarianceProof`, `Representation.Operations`

## Exclusion audit

### Mechanical checks over the whole closure

1. **Excluded names.** The names of all 603 modules and their Lean sources
   were scanned for: `HighestDerivativeSupportShift` (with `…Boundary` and
   `…Proof`), `SegmentSocleDerivatives`,
   `NonjuxtaposedSegmentSocleConstituentLevel`,
   `NonjuxtaposedSegmentSocleDerivativeStrictMono`,
   `SegmentSocleProductHighestDerivative`, `TwoSupercuspidal`,
   `ProductDualTwist`, `twoBlockFactors`, `SegmentHeadProductIrreducibility`,
   `UnlinkedSegmentSocleProductIrreducible`,
   `LinkedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSoclePairReducible`,
   `JuxtaposedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSocleReverseProductQuotientHom`,
   `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
   `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
   `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
   `GenericSegmentProductUniqueness`,
   `SquareIntegrableLanglandsClassification`,
   `SegmentSpecialEssentialSquareIntegrability`, `SegmentFullJacquetFormula`,
   `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
   `SegmentSpecialJacquetExponentNormFormula`,
   `SupercuspidalCoinvariantFiniteness`, `IrreducibleCoinvariantFiniteness`,
   `LeviCuspidalCoinvariantFiniteness`, `MirabolicFiniteLength`,
   `MinusExactness`, `GeneralLinearDerivativeExactness`, `Leibniz`,
   `SupercuspidalDerivatives`, `SupercuspidalDerivativeVanishing`,
   `TwistedProductOrdinaryDual`, `TwistedProductCharacterTwist`,
   `UnitaryGenericCompatibility`, `SegmentDerivative`, `SegmentProduct`,
   `MirabolicModulusStatement`, `MirabolicRadicalHaarModulus` (the
   Haar-modulus comparison), `Exponents`, `PersistenceTransport` and
   `MaximalCone`. The only hits are two comments of
   `Classification.CuspidalProductContragredient`. They credit the model
   proofs in `TwistedProductCharacterTwistProof` and
   `TwistedProductOrdinaryDualProof`; neither is imported. The broader words
   `Multisegment`, `Socle`, `SquareIntegrable`, `Tempered`, `SpecialHead` and
   `Exhaustion` were also scanned. They occur only in:
   - the definitions `Multisegment` and `IsIrreducibleSocle` of the
     definition modules `Classification.Segments` and
     `Classification.ConstituentRelations`;
   - the word "exhaustion" (by compact open subgroups), in comments and section
     names of `CompactCoefficient.AdmissibleComplement`,
     `Jacquet.CharacterAveraging` and `Parabolic.GeometricPrerequisitesStatement`.
2. **Identifiers of excluded results.** The Lean and Markdown files of the
   closure were searched for the recorded identifiers of the excluded results
   and admitted inputs (not their Lean names, which check 1 covers). The Lean
   files contain none. In Markdown they occur only in records of exclusions or
   provenance:
   - the target statement's Markdown;
   - the two helpers of this proof;
   - the 4.7(a) helper (written for the proof of `HighestDerivativeSupportShift`);
   - the independence audits of `Derivative.TopLocalizationData`,
     `Jacquet.LocalizationTower`, `Derivative.PartialDerivativeJacquetLHS`,
     `Derivative.PartialDerivativeJacquetNormalization`,
     `Derivative.MirabolicDerivativeVanishing`,
     `Derivative.MirabolicHighestDerivativeDescent` and
     `Derivative.MirabolicHighestDerivativePairingProof`;
   - the provenance notes of `Derivative.MinusVanishing` and
     `Derivative.MirabolicPhiMinusNondegeneratePairing`. These are helpers of
     the two admitted inputs, the BZ77 §4.4 proof and the BZ77 3.8 pairing
     proof; `MinusVanishing` is the BZ77 3.2(e) vanishing consequence, not §4.4.
3. **Proof modules.** 441 closure modules are the main modules of published
   statements, definitions and proofs: 138 proofs, 120 statements and 183
   definitions. Of the 138 proof modules, the only one that proves a result
   named in the conditions or exclusions below is the BZ77 3.8 pairing proof
   (`Derivative.MirabolicHighestDerivativePairingProof`), a required input.
   The other 162 modules are the two
   helpers, `CuspidalSupport.WholeLeviTransport`, and basic definitions and
   infrastructure (groups, fields, smooth representations, contragredients,
   twists, measures, Hecke and Jacquet basics, the Gelfand–Kazhdan Whittaker
   setting). Checks 1 and 2 cover them.
4. **Statement modules.** The closure contains proposition definitions such as
   `Derivative.MirabolicDerivativeDetectionStatement`,
   `Classification.CuspidalJacquetMultiplicityStatement`,
   `Whittaker.PrerequisitesStatement`, `RankinSelberg.AnalyticStatement` and
   `Jacquet.ExactStatement`. They are imported as types by published modules.
   The final theorem takes no hypothesis, so no unproved proposition is
   assumed.

### Required inputs

| Condition | Result |
| --- | --- |
| BZ77 3.8 only through `Derivative.mirabolicHighestDerivativePairing` | Used exactly there, in `exists_derivative_hom_contragredient` (helper 2). |
| BZ77 §4.4 only through its published proof | Not used. Neither `Classification.SupercuspidalDerivativesProof`, its statement, nor `Classification.SupercuspidalDerivativeVanishing` is in the closure. The 4.7(a) helper replaces §4.4 by cuspidal Jacquet vanishing. |
| GL Leibniz filtration only through its published proof | Not used; no Leibniz module is in the closure. |
| Exactness of derivatives only through published proofs of the two exactness statements | Not used. Neither statement module is in the closure. The closure has exactness of the Jacquet functor and of the smooth contragredient, which are distinct published results. |
| Lemma 4.7(a) | Quotient form from the published helper `CuspidalProductDerivativeQuotientSupport`, plus published support uniqueness. |
| Finite length of derivatives | Not used: the proof uses no Jordan–Hölder series. |
| Contragredient of a product, for every `r` and all ranks | Proved in helper 1. |
| Support of a contragredient | Proved in helper 1 (`isSupercuspidalSupport_contragredient`). |
| Pairing to Jordan–Hölder constituent | Replaced by the nonzero map `π̄^(k) → σ̃` (helper 2) and the quotient form of 4.7(a). |
| Haar-modulus comparison | Not used; the pairing covariance is `|det|` in the Library convention. |
| No theorem-valued hypothesis or conditional proof | The theorem has no premise. Its inputs are published results and the two helpers of this proof. |

### Exclusions

| Exclusion | Result |
| --- | --- |
| `HighestDerivativeSupportShift`, its proofs, `HighestDerivativeSupportShiftBoundary` | Not imported. `Classification.SegmentSocleDerivativesStatement`, `…Boundary` and any `HighestDerivativeSupportShiftProof` are absent from the closure. The only module written for the proof of `HighestDerivativeSupportShift` is the 4.7(a) helper `CuspidalProductDerivativeQuotientSupport`, used as described above. |
| Segment-socle derivative statements | `SegmentSocleDerivatives`, `NonjuxtaposedSegmentSocleConstituentLevel`, `NonjuxtaposedSegmentSocleDerivativeStrictMono` and `SegmentSocleProductHighestDerivative` occur nowhere in the closure. |
| Two-supercuspidal product conclusions (`TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure`) | No `TwoSupercuspidal*` module. `TwoSupercuspidalProductDualTwist` is replaced by helper 1. |
| Segment derivative and segment product formulas | None. The only segment module is the definition module `Classification.Segments`, used for `CuspidalDatum.twist`. |
| Whittaker coinvariant finiteness and `MirabolicFiniteLength` | No such module. The Whittaker modules in the closure are the Gelfand–Kazhdan character, measure and Iwasawa infrastructure used by the published 3.8 pairing proof. |
| Ze80 6.1(a), linked pairs, final product criteria, classification | None. No such module or name is in the closure. |

### Exclusions inherited from the Ze80 §6.2 homogeneity proof

These are the conclusions, proofs and transitive dependencies of:

- `OrderedMultisegmentSocleExistence`, socle exhaustion, analytic segment
  classification, the segment-socle product results
  (`UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSoclePairReducible`), `SegmentSocleProductIrreducibility`,
  `SegmentHeadProductIrreducibility`, special-head exhaustion, ordered
  special-head existence, quotient coverage, tempered block uniqueness,
  `SquareIntegrableLanglandsClassification`, square-integrable exhaustion,
  regular exhaustion, `GenericSegmentProductUniqueness`, ordered conversion
  and forward special-segment essential square-integrability;
- `AdjacentUnlinkedSegmentSocleSwap` and `TwoSegmentSocleCommutation`;
- the nonadjacent-consumer list: individual segment-socle and special-head
  existence, `AdjacentUnlinkedSegmentSocleSwap` and the segment Jacquet
  formulas;
- the bans on Ze80 §3.5/§9.6 derivative formulas, segment irreducibility
  criteria, Ze80 9.3, and classification or exhaustion theorems.

Result: by check 1 no corresponding module or declaration name occurs in the
closure. By check 2 none of their identifiers occurs outside exclusion
records. By check 3 no published proof in the closure proves one of them. The
mathematical route (steps 1–7, and the 4.7(a) helper's route) uses no segment,
socle, head, irreducibility criterion, classification, exhaustion or
square-integrability result. Every derivative result used has a
published proof: the BZ77 3.8 pairing, and Ze80 3.7(b) inside the 4.7(a)
helper.

### Exclusions inherited from the proof of `HighestDerivativeSupportShift`

- **Independence.** The excluded results are
  `UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSoclePairReducible`,
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
  `TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
  `OrderedMultisegmentSocleExistence`, socle exhaustion, analytic segment
  classification, special-head exhaustion, ordered special-head existence,
  quotient coverage, ordered conversion, tempered block uniqueness,
  `GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
  square-integrable exhaustion, regular exhaustion and forward
  special-segment essential square-integrability, with their named
  conclusions, and the special-head criterion
  `SegmentHeadProductIrreducibility`. Absent, by checks 1–3.
- **BZ77-only.** This bans segment derivative formulas, segment socle and
  head existence and their Jacquet formulas, segment classification, the
  segment-socle derivative statements, the two-supercuspidal product
  conclusions, and the consumer list repeated there. Absent, as above.
- **Extra clauses.** `HighestDerivativeSupportShift` and every proof of it
  are excluded. Only the helper `CuspidalProductDerivativeQuotientSupport`
  is used, as recorded above.

### Shared upstream restrictions

- **Shared upstream scope.** This bans Whittaker supercuspidal coinvariant
  finiteness (`Whittaker.SupercuspidalCoinvariantFinitenessStatement`), and
  `GenericSegmentProductUniqueness`, special-head exhaustion, ordered
  special-head existence, quotient coverage, ordered conversion, tempered
  block uniqueness, `SquareIntegrableLanglandsClassification`,
  square-integrable exhaustion and regular exhaustion. Absent, by checks 1–3.
  No missing derivative or tensor proof is replaced by a consumer assumption.
- **Restrictions of the BZ77 §4.4 proof.** The independence and BZ77-only
  restrictions are the same as for the proof of `HighestDerivativeSupportShift`
  above. Shared lower inputs are
  reused only after this audit: the geometric lemma, cuspidal support,
  Jacquet functors and derivative functors. No derivative exactness, Leibniz
  filtration or finite length is used.
- **Whittaker-finiteness independence.** This bans
  `IrreducibleCoinvariantFinitenessStatement`,
  `LeviCuspidalCoinvariantFinitenessStatement` and the
  `MirabolicFiniteLength` route. Absent, by checks 1–3.

### The two shared modules

- `Classification.CuspidalProductDerivativeQuotientSupport`. Its closure has
  369 modules, including itself and `WholeLeviTransport`; all are part of the
  closure above and covered by the checks. Its own audit found no excluded
  input. Its proof uses the
  published inputs of its Markdown table and no other result written for the
  proof of `HighestDerivativeSupportShift`.
- `CuspidalSupport.WholeLeviTransport`. It imports three published
  `CuspidalSupport` proof and definition modules and proves the two transport
  theorems that were published in `Exponents.PersistenceTransport`. No
  `Exponents` module or `MaximalConeLifting` is in the closure.
