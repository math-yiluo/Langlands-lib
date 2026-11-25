# Cuspidal Jacquet modules of a product of two segment socles on one line, proof

This module is the final assembly. It
copies no code: every input is a published declaration imported by Lean name.
The shuffle-filtration assembly is `TwoSegmentShuffleAssembly`, and the
surviving-piece computation is `TwoSegmentShufflePieces`. The proof
of Ze80 3.1 is the published `segmentFullJacquetFormula` of
`SegmentFullJacquetProof`.

## Statement proved

```lean
theorem Langlands.Classification.twoSegmentSocleShuffleJacquet
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSegmentSocleShuffleJacquet.{uF, uV, uW} F T
```

The theorem proves the published proposition
`Langlands.Classification.TwoSegmentSocleShuffleJacquet.{uF,uV,uW} F T` of
`Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetStatement`.
The statement pair and every pair it
imports are unchanged. The outer telescope is exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and
the theorem has no further hypothesis and no theorem-valued premise. The
universes `uF`, `uV` and `uW` are independent level parameters; none is
saturated. Inspection of the theorem reports `level_parameters = [uF, uV, uW]`
and the axioms `propext`, `Classical.choice` and `Quot.sound` only.

The proposition says the following. Take a cuspidal datum `ρ` of rank `r` with
an actual supercuspidal representative `A`, reals `a₀, a₁`, naturals `m₀, m₁`
and a datum `d : T.SegmentProductDatum.{uV,uF} ((m₀ + m₁) * ρ.rank)` with
`d.length = 2` and `d.HasSegmentSocles`. Suppose segment `0` has beginning
`ρ.twist a₀` and length `m₀`, and segment `1` has beginning `ρ.twist a₁` and
length `m₁`. Let `C = BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos` and
`J = CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj`. Then

1. `HasCompositionSeriesLength J ((m₀ + m₁).choose m₀)`, and
2. for every irreducible `τ` of `C.Levi F.Carrier` on a carrier in universe
   `uW` and every `m`, `HasJordanHolderMultiplicity J (Rep.of τ) m` holds iff
   `m` is the number of `S : Finset (Fin (m₀ + m₁))` with `S.card = m₀` whose
   shuffle tensor
   `FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S a₀ a₁)`
   is equivalent to `τ`.

Since the theorem has exactly this type, it claims nothing beyond the
statement's Markdown.

## Implemented proof

The module contains two declarations.

```lean
theorem TwoSegmentShuffle.survivingPieceEquiv_of_segmentSubrepresentationFullJacquet
    (h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T) :
    SurvivingPieceEquiv.{uF, uV} F T :=
  fun _ A a₀ a₁ _ _ d h₂ hA hsoc hb₀ _ hb₁ _ h₀ h₁ w S R hS hR hdiv =>
    surviving_piece_equiv F T h31 A hA a₀ a₁ d h₂ hsoc hb₀ hb₁ h₀ h₁ w S R hS hR hdiv

theorem twoSegmentSocleShuffleJacquet ... :
    TwoSegmentSocleShuffleJacquet.{uF, uV, uW} F T :=
  TwoSegmentShuffle.twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv F T
    (TwoSegmentShuffle.survivingPieceEquiv_of_segmentSubrepresentationFullJacquet F T
      (segmentFullJacquetFormula.{uF, uV} F T).1)
```

The first theorem is a bridge between the two supporting modules. Its body only
reorders binders. `SurvivingPieceEquiv` (module `TwoSegmentShuffleAssembly`)
quantifies over the data of the target statement in its binder order. The
pointwise `surviving_piece_equiv` (module `TwoSegmentShufflePieces`) takes
explicit arguments and does not need the two length equations, which the
bridge discards. The second theorem feeds clause 1 of the published
`segmentFullJacquetFormula` (Ze80 3.1,
`SegmentSubrepresentationFullJacquet`) to the bridge and then to the
conditional assembly `twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv`.
`segmentFullJacquetFormula` is used at universes `uF, uV`, the universes of
`SurvivingPieceEquiv`. The assembly theorem is universe-polymorphic in `uW`.

The mathematical route, implemented in the two supporting modules, follows
Zelevinsky 1980, 1.6 and 3.1. Write `r = ρ.rank`, `B = d.shape` for the
two-block shape `(m₀ r, m₁ r)`, and `σ₀, σ₁` for the socles `d.blocks`.

1. *Geometric lemma* (`TwoSegmentShuffleAssembly.shuffleJacquet_of_pieces`).
   The published `Geometric.padicGeometricLemma`, at carrier universe
   `max uF uV`, filters `J = r_C(i_B(σ₀ ⊗ σ₁))` by the minimal double-coset
   representatives `w` for `(B, C)`. The graded piece of `w` is the geometric
   piece `(geometricPieceFunctor T B C w S R hS hR).obj (σ₀ ⊗ σ₁)`.
2. *Vanishing* (`geometricPiece_subsingleton_of_not_dvd`). If some piece of
   the source refinement `S` has size not divisible by `r`, the normalized
   Jacquet module of the corresponding socle along that refinement is zero
   (`IsSegmentSocle.jacquet_subsingleton_of_not_dvd`, the vanishing in the proof
   of Ze80 3.4). So the whole geometric piece is zero
   (`SegmentEdge.refinedJacquet_external_subsingleton`,
   `SegmentEdge.geometricPiece_subsingleton`).
3. *Surviving pieces* (`TwoSegmentShufflePieces.surviving_piece_equiv`).
   If every piece of `S` has size divisible by `r`, the conjugated
   intersection Levi is the Levi of `C`
   (`ShuffleRefinement.conjugatesLevi_flatten_uniform`). Then the piece is the
   transport along `w` of the refined Jacquet module of `σ₀ ⊗ σ₁`
   (`Geometric.wholeLeviGeometricPieceEquiv`). That module is the tensor of the
   Jacquet modules of `σ₀` and `σ₁` (`RefinedJacquetTensor.jacquetEquiv`). By
   Ze80 3.1 (`h31`; `IsSegmentSocle` implies `IsSegmentSubrepresentation`) the
   Jacquet module of `σⱼ` along its uniform refinement is
   `⊗ᵢ ν^i A'` (`segmentFactors A'`, factors `A', νA', …`) for a
   representative `A'` of the segment base `ρ.twist aⱼ`. Then
   `JuxtaposedShuffle.nonempty_cast_iso` identifies each `ν^i A'` with
   `ν^(aⱼ+i) A`, so this Jacquet module is `⊗ᵢ ν^(aⱼ+i) A`.
   The transport `CuspidalSupport.transportEquiv` and
   `ShuffleRefinement.uniformRefinementTensorEquiv` reorder the nested tensor
   into the shuffle tensor of the subset
   `S' = ShuffleRefinement.refinementShuffle … w S …`. The exponents agree by
   `shuffleExponent_refinementTargetIndex_zero` and `_one`.
4. *Deletion and indexing.* `ObjectRepFiltration.zeroFactorDeletionTheorem`
   deletes the zero pieces. `ShuffleRefinement.divisibleEquivShuffles`
   identifies the surviving representatives with
   `{S : Finset (Fin (m₀ + m₁)) // S.card = m₀}`, compatibly with
   `refinementShuffle`.
5. *Counting.* Each shuffle tensor is irreducible
   (`shuffleTensor_isIrreducible`, from `CuspidalSupport.glCuspidalTensor`).
   `finiteFamilyFiltrationMultiplicity` gives a composition series of length
   `Nat.card {S // S.card = m₀} = (m₀ + m₁).choose m₀`
   (`Fintype.card_finset_len`). It also gives the Jordan–Hölder multiplicity of
   every `τ` in universe `uW` as the number of shuffles whose tensor is
   equivalent to `τ`.

The Markdown files of `TwoSegmentShuffleAssembly` and `TwoSegmentShufflePieces`
describe each step with its hypotheses.

## Scope

The theorem keeps arbitrary primes, finite p-adic fields, the supplied
compatible topology `T`, arbitrary real `a₀, a₁` and natural `m₀, m₁`, and
repeated, equal and linked segments. It uses the actual upper normalized
product induction `d.induced` and the actual upper normalized Jacquet module
`upperJacquet`. It adds no finite-length, irreducibility, genericity, linkage or
distinctness premise. The socles have carriers in `max uF uV`, and the geometric
lemma is used at that universe. `τ` ranges over carriers in the independent
universe `uW`.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980): §1.6
  (printed pp. 171–172), the coordinate form of the geometric lemma; §3.1
  (printed pp. 180–181), the Jacquet module of `⟨Δ⟩`; the proof of
  Proposition 3.4 (printed p. 181), the vanishing along compositions that are
  not made of multiples of `r`. Literature ID `zelevinsky-1980-induced-ii`,
  SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 2.12, the geometric lemma
  (printed p. 448). Literature ID `bernstein-zelevinsky-1977-induced-i`.

The Lean route follows the four steps of these sources. The piece
identification goes through the whole-Levi transport and the refined Jacquet
tensor equivalence of the Library rather than Zelevinsky's matrix notation.

## Dependency audit

All counts and checks below refer to Library commit
`fcac121256163a8da6dd01a9483e1104a9b92aba`. Module names in tables omit the
prefix `Langlands.`.

### Direct inputs

| Input (module) | Use |
| --- | --- |
| `segmentFullJacquetFormula` (`Representation.Classification.SegmentFullJacquetProof`) | Clause 1 is Ze80 3.1, `SegmentSubrepresentationFullJacquet`. It is imported as proved, not duplicated. |
| `TwoSegmentShuffle.SurvivingPieceEquiv`, `twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv` (`Representation.Classification.TwoSegmentShuffleAssembly`) | Geometric-lemma filtration, vanishing, deletion, indexing and counting, conditional on `SurvivingPieceEquiv`. |
| `TwoSegmentShuffle.surviving_piece_equiv` (`Representation.Classification.TwoSegmentShufflePieces`) | Surviving pieces, conditional on Ze80 3.1. |

The geometric lemma `Geometric.padicGeometricLemma`
(`Representation.Geometric.GeometricLemmaProof`) is the other main input.
`TwoSegmentShuffleAssembly` uses it, and it is not duplicated. The two
supporting modules list their own direct inputs in their Markdown.

### Import closure

A recursive scan of the `import` lines gives 1055 project modules in the
transitive closure, this module included. The closure of each direct import:

- `SegmentFullJacquetProof`: 1038 modules. It contains the closure of Ze80 1.11,
  `TwoSupercuspidalProductStructureProof`, with 879 modules.
- `TwoSegmentShuffleAssembly`: 373 modules.
- `TwoSegmentShufflePieces`: 183 modules.

Their union is the whole closure except this module.

### Exclusions

The checks below show that the closure is independent of the later results of
the classification named in the next item.

- *Declaration names.* No Lean file of the closure contains any of the names
  `LinkedSegmentSocleReverseProductStructure`,
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `LinkedSegmentSocleReverseProductSteps`, `LinkedSegmentSoclePairReducible`,
  `SegmentSocleProductIrreducibility`, `UnlinkedSegmentSocleProductIrreducible`,
  `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
  `TwoFactorProductConstituentCommutativity`, `LinkedSegmentSocleGluing`,
  `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
  `SegmentEssentialSquareIntegrableClassification`,
  `MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
  `OrderedMultisegmentQuotientExhaustion`, `TemperedBlockUniqueness`,
  `SquareIntegrableLanglandsClassification`,
  `SquareIntegrableLanglandsExhaustion`, `GLRegularLanglandsExhaustion`
  or `SegmentHeadProductIrreducibility`. These are the later results of the
  classification that this proof is independent of.

Supporting modules of a later result. Nine finite supporting modules of
`JuxtaposedSegmentSocleReverseProductStructure` lie in the closure:

| Module |
| --- |
| `Representation.Classification.JuxtaposedRefinementTools` |
| `Representation.Classification.TwoSourceShuffleLabels` |
| `Representation.Classification.UniformJacquetVanishing` |
| `Representation.Classification.UniformRefinementCombinatorics` |
| `Representation.Classification.UniformRefinementCoordinates` |
| `Representation.Classification.UniformRefinementLeviTransport` |
| `Representation.Classification.UniformRefinementShuffleRealization` |
| `Representation.Classification.UniformRefinementSurvivors` |
| `Representation.Classification.UniformTargetBlockLabels` |

They contain finite coordinates, shuffle labels, Levi and tensor transport,
twist transport and the vanishing of Jacquet modules of segment socles along
shapes with a part not divisible by the cuspidal rank. They are upstream
inputs of that structure theorem, not its exact proof or one of its
conclusions. Their closures lie inside the closure audited here, so they
contain no statement, proof or name of a result listed above. They assume neither
`JuxtaposedSegmentSocleReverseProductStructure` nor any other of those results.
The audits of
`TwoSegmentShuffleAssembly` and `TwoSegmentShufflePieces` record the same
finding. Since none of them imports this module, there is no circularity.

Two lower modules were written as infrastructure for the socle exhaustion
`MultisegmentSocleExhaustion`:

- `Representation.Filtration.ObjectTransport`.
  It pulls an `ObjectRepFiltration` back along a monoid homomorphism and
  transports it along an equivalence. Its only import is
  `Filtration.LengthTwoMatching`. The supporting modules reach it through
  `Tensor.ProductFiltration`, which `SegmentEdgeJacquetReduction` imports. The
  1.11 and 3.1 closures also reach it through `NonadjacentSpecialization` and
  `OppositeCuspidalJacquetFiltrationProof`.
- `Combinatorics.RelationInversions`. It counts inversions of a decidable relation on finite lists, and
  it imports only Mathlib. It is reached only inside the 1.11 closure, through
  `Group.GL.UpperBruhatFiltration`.

Both are generic infrastructure that asserts no representation-theoretic
theorem. Neither is a conclusion or proof of `MultisegmentSocleExhaustion`, and
neither imports anything else written for it.

### Derivative results

This module and its two supporting modules state, construct and prove nothing
about derivatives. Neither supporting-module closure contains a module named
`Derivative`, `Mirabolic` or `GelfandKazhdan`. Their only module named
`Whittaker` is `Whittaker.Iwasawa`, the Iwasawa decomposition of `GL_n`.

This module uses the published proof of `SegmentFullJacquetFormula` as an input.
That proof uses Ze80 1.11 (`twoSupercuspidalProductStructure`), which proves
BZ77 Theorem 4.2 with the Bernstein–Zelevinsky
derivative theory. So the 1.11 closure contains 158 modules named
`Derivative`, `Mirabolic`, `Whittaker` or `GelfandKazhdan`, and all of them lie
inside it. They include the derivative functors and their exactness
(`Derivative.GeneralLinearDerivativeExactnessProof`), the BZ77 4.13–4.14
product and Leibniz filtrations (the `Derivative.MirabolicProductMinus…`
modules of the first table below, `Derivative.LeftMixedProductDerivativeProof`,
`Derivative.RightMixedProductDerivativeFiltrationProof` and
`Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`), and the
supercuspidal derivative vanishing and one-dimensional top derivative of BZ77
4.4 (`Classification.SupercuspidalDerivativesProof`). They also include
Whittaker multiplicity one (`Whittaker.MultiplicityOneProof`) and the
Gelfand–Kazhdan realization (`Smooth.Contragredient.GelfandKazhdanProof`).
Every one of these is proved in the Library, and none is a hypothesis of
any step. They enter this proof only through the input
`SegmentFullJacquetProof`. This module neither duplicates them nor uses
them directly.

The closure contains no segment derivative formula. A text search for
`SegmentSocleDerivatives`, `HighestDerivativeSupportShift`,
`NonjuxtaposedSegmentSocleConstituentLevel`, `SegmentHeadJacquetFormula` and
`SegmentSocleJacquetFormula` over its Lean files finds nothing. No module of
the closure belongs to the proofs of Ze80 3.5, Ze80 4.3, BZ77 4.7(b), the
highest derivative of segment-socle products, or the segment derivative
statements of `SegmentSocleDerivativesStatement`. The Markdown of
`SegmentFullJacquetProof`, section "Derivative results", records the
corresponding audit of the 1.11 route. That route is a fully proved BZ77
derivative route, without Ze80 3.5 or 9.6 and without the later results
listed above.

### Proved-module inventory

The first table lists the 247 closure modules that are the entry modules of
published proofs. None of them is a proof of one of the later results listed
above.

| Proved module |
| --- |
| `Algebra.SandwichDimensionBoundProof` |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` |
| `Analysis.Local.QuotientAutomorphismProof` |
| `Analysis.Local.QuotientAveragingKernel` |
| `Analysis.Local.QuotientMeasureExistence` |
| `Analysis.Local.QuotientPositiveLifting` |
| `Galois.Local.AbsoluteProof` |
| `Group.GL.BlockContractionProof` |
| `Group.GL.BlockIwahoriBasis` |
| `Group.GL.BlockModulusHaarProof` |
| `Group.GL.BlockUnipotentHaarProof` |
| `Group.GL.CartanProof` |
| `Group.GL.CentralQuotientTopologyProof` |
| `Group.GL.CountabilityProof` |
| `Group.GL.InverseTransposeIwahoriProof` |
| `Group.GL.MirabolicMixedOrbitCoverageProof` |
| `Group.GL.MirabolicModularCharacterProof` |
| `Group.GL.MirabolicModulusProof` |
| `Group.GL.PrincipalBlockFactorizationProof` |
| `Group.GL.UpperBruhatBoundaryProof` |
| `Group.GL.UpperBruhatCoordinatesProof` |
| `Group.GL.UpperBruhatFiltrationGeometryProof` |
| `Group.GL.UpperBruhatLocalClosednessProof` |
| `Group.GL.UpperBruhatPivotProof` |
| `Group.GL.UpperBruhatProof` |
| `Group.GL.UpperBruhatRankProof` |
| `Group.GL.UpperBruhatTransposeProof` |
| `Group.GL.UpperUnipotentCompactContainmentProof` |
| `Group.GL.UpperUnipotentFactorizationProof` |
| `HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof` |
| `HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof` |
| `HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof` |
| `HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof` |
| `HarmonicAnalysis.Distribution.ClosedRestrictionProof` |
| `HarmonicAnalysis.Distribution.ClosedSupportedDescentProof` |
| `HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof` |
| `HarmonicAnalysis.Distribution.HomogeneousPositivityProof` |
| `HarmonicAnalysis.Distribution.HomogeneousVanishingProof` |
| `HarmonicAnalysis.Distribution.LocalizationProof` |
| `HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof` |
| `HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof` |
| `HarmonicAnalysis.Distribution.TransposeInvariantProof` |
| `HarmonicAnalysis.PadicAdditiveConductorProof` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` |
| `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` |
| `HarmonicAnalysis.RowTensorDecompositionProof` |
| `HarmonicAnalysis.RowTestSmoothProof` |
| `HarmonicAnalysis.TriangularTranslationProof` |
| `LinearAlgebra.CyclicQuotientPairingProof` |
| `LinearAlgebra.MatrixAEvalConjugacyProof` |
| `LinearAlgebra.MatrixCharpolyConjugacyProof` |
| `LinearAlgebra.MatrixTransposeConjugateProof` |
| `LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof` |
| `LocalField.SmoothCharacterNormProof` |
| `Representation.Character.SeparationProof` |
| `Representation.Character.TransportProof` |
| `Representation.Classification.ConstituentCompatibilityAlgebraicProof` |
| `Representation.Classification.CuspidalIntegralTwistFreenessProof` |
| `Representation.Classification.IrreducibleProductEmbedding` |
| `Representation.Classification.IrreducibleTwoFactorProductSwapProof` |
| `Representation.Classification.OppositeCuspidalJacquetFiltrationProof` |
| `Representation.Classification.SegmentConstituentCentralCharacterProof` |
| `Representation.Classification.SegmentFullJacquetProof` |
| `Representation.Classification.SegmentInductionAdmissibilityProof` |
| `Representation.Classification.SegmentTensorStabilizerProof` |
| `Representation.Classification.SupercuspidalContragredientProof` |
| `Representation.Classification.SupercuspidalDerivativesProof` |
| `Representation.Classification.TwistedProductCharacterTwistProof` |
| `Representation.Classification.TwoBlockExponentNonUnitarizabilityProof` |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof` |
| `Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` |
| `Representation.Classification.TwoSupercuspidalProductStructureProof` |
| `Representation.CompactCoefficient.SemisimplicityProof` |
| `Representation.Conductor.PrincipalCongruenceBasisProof` |
| `Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesProof` |
| `Representation.CuspidalSupport.AssociatedProof` |
| `Representation.CuspidalSupport.AssociationLawsProof` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessProof` |
| `Representation.CuspidalSupport.CuspidalEmbeddingProof` |
| `Representation.CuspidalSupport.CuspidalTensorAssociationProof` |
| `Representation.CuspidalSupport.CuspidalTensorProof` |
| `Representation.CuspidalSupport.CuspidalityComparisonProof` |
| `Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof` |
| `Representation.CuspidalSupport.DeterminantUnitStructureProof` |
| `Representation.CuspidalSupport.DistinctTensorStabilizerProof` |
| `Representation.CuspidalSupport.FiltrationQuasicuspidality` |
| `Representation.CuspidalSupport.HarishChandraAssembly` |
| `Representation.CuspidalSupport.HarishChandraBoundaryProof` |
| `Representation.CuspidalSupport.HarishChandraConverseProof` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` |
| `Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` |
| `Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof` |
| `Representation.CuspidalSupport.LeviTensorFactorizationProof` |
| `Representation.CuspidalSupport.LeviTensorReflectionProof` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` |
| `Representation.CuspidalSupport.MinimalJacquetProof` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` |
| `Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof` |
| `Representation.CuspidalSupport.ProperInductionProof` |
| `Representation.CuspidalSupport.QuasicuspidalEmbeddingProof` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` |
| `Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` |
| `Representation.CuspidalSupport.StandardJacquetComparisonProof` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` |
| `Representation.CuspidalSupport.ZeroRankEmbeddingProof` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessProof` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` |
| `Representation.Derivative.LeftMixedProductDerivativeProof` |
| `Representation.Derivative.MirabolicDerivativeDetectionProof` |
| `Representation.Derivative.MirabolicHighestDerivativePairingProof` |
| `Representation.Derivative.MirabolicMinusExactnessProof` |
| `Representation.Derivative.MirabolicMinusPairingTransferProof` |
| `Representation.Derivative.MirabolicProductMinusBoundary` |
| `Representation.Derivative.MirabolicProductMinusLeftPhi` |
| `Representation.Derivative.MirabolicProductMinusLeftPsi` |
| `Representation.Derivative.MirabolicProductMinusRightBoundary` |
| `Representation.Derivative.MirabolicProductMinusRightPhi` |
| `Representation.Derivative.MirabolicProductMinusRightPsi` |
| `Representation.Derivative.MirabolicProductRestriction` |
| `Representation.Derivative.RightMixedProductDerivativeFiltrationProof` |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` |
| `Representation.Filtration.GradedRefinementProof` |
| `Representation.Filtration.IntervalLiftProof` |
| `Representation.Filtration.IrreducibleMultiplicityProof` |
| `Representation.Filtration.JordanHolderComparisonProof` |
| `Representation.Filtration.JordanHolderProof` |
| `Representation.Filtration.JordanHolderTransportProof` |
| `Representation.Filtration.LengthCriterionProof` |
| `Representation.Filtration.LengthTwoMatching` |
| `Representation.Filtration.MultiplicityIndependenceProof` |
| `Representation.Filtration.MultiplicityTransportProof` |
| `Representation.Filtration.QuasicuspidalVanishingProof` |
| `Representation.Filtration.SubsingletonProof` |
| `Representation.Filtration.ZeroFactorDeletionProof` |
| `Representation.Geometric.BlockSixDecomposableProof` |
| `Representation.Geometric.BruhatMatrixExistenceProof` |
| `Representation.Geometric.BruhatWeylReflectionProof` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` |
| `Representation.Geometric.GeometricLemmaProof` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` |
| `Representation.Geometric.MonotoneBlocksProof` |
| `Representation.Geometric.OrbitSectionExtensionProof` |
| `Representation.Geometric.PadicCorrectionCancellationProof` |
| `Representation.Geometric.PadicParabolicBruhatProof` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` |
| `Representation.Geometric.ParabolicSupportGradedProof` |
| `Representation.Geometric.ParabolicSupportJacquetProof` |
| `Representation.Geometric.StandardIntersectionsProof` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` |
| `Representation.Geometric.WeylUniquenessProof` |
| `Representation.Hecke.CommonInvarianceProof` |
| `Representation.Induction.CharacterTwistProof` |
| `Representation.Induction.CompactAutomorphismIntegralProof` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` |
| `Representation.Induction.CompactLocalSectionSpanningProof` |
| `Representation.Induction.CompactQuotientProof` |
| `Representation.Induction.CompactScalarProof` |
| `Representation.Induction.CompactSurjectivityProof` |
| `Representation.Induction.CompactTransitivityProof` |
| `Representation.Induction.FiniteProductTensorBijectiveProof` |
| `Representation.Induction.NormalCoinvariantKernelProof` |
| `Representation.Induction.NormalCoinvariantProof` |
| `Representation.Induction.OppositeProductReversalProof` |
| `Representation.Induction.SplitQuotientProof` |
| `Representation.Induction.SplitStagesCharacterComparison` |
| `Representation.Induction.SurjectivityProof` |
| `Representation.Jacquet.BlockCompressionProof` |
| `Representation.Jacquet.BlockPowerKernelProof` |
| `Representation.Jacquet.CanonicalLiftBijectivityProof` |
| `Representation.Jacquet.CanonicalLiftGroupTransportProof` |
| `Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof` |
| `Representation.Jacquet.CompactCompressionStableDualityProof` |
| `Representation.Jacquet.CompressionStabilizationProof` |
| `Representation.Jacquet.ExactProof` |
| `Representation.Jacquet.LocalizationExactnessProof` |
| `Representation.Jacquet.OppositeCanonicalLiftProof` |
| `Representation.Jacquet.ReciprocityProof` |
| `Representation.Jacquet.RefinedOppositeCanonicalLiftProof` |
| `Representation.Jacquet.RefinedOppositeCompressionProof` |
| `Representation.Jacquet.RefinedOppositePowerKernelProof` |
| `Representation.Jacquet.RefinedOppositeStableImageProof` |
| `Representation.MatrixCoefficient.NormRegularityProof` |
| `Representation.Parabolic.InverseTransposeProductProof` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` |
| `Representation.Parabolic.NaturalInductionDualityProof` |
| `Representation.Parabolic.NaturalJacquetDualityProof` |
| `Representation.Parabolic.NormalizedAdmissibilityProof` |
| `Representation.Parabolic.NormalizedJacquetAdmissibilityProof` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` |
| `Representation.Parabolic.OppositeJacquetAdmissibilityProof` |
| `Representation.Parabolic.OppositeRefinementTransitivityProof` |
| `Representation.Parabolic.OrderedProductRegroupingProof` |
| `Representation.Parabolic.QuotientCompactProof` |
| `Representation.Parabolic.RefinedInductionTensorProof` |
| `Representation.Parabolic.RefinementCoordinatesNormalizationProof` |
| `Representation.Parabolic.RefinementInductionTransitivityProof` |
| `Representation.Parabolic.SecondAdjointnessProof` |
| `Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof` |
| `Representation.Parabolic.UnipotentFiniteContainment` |
| `Representation.RankinSelberg.EqualRankFrobeniusProof` |
| `Representation.RankinSelberg.GeneralLinearUnimodularity` |
| `Representation.RankinSelberg.HaarSymmetriesProof` |
| `Representation.RankinSelberg.LastRowCompactOrbitProof` |
| `Representation.RankinSelberg.UnipotentUnimodularity` |
| `Representation.RankinSelberg.ZeroRowLastRowCutoffProof` |
| `Representation.Schur.CountableDimensionProof` |
| `Representation.Smooth.Contragredient.AdmissibleDualityProof` |
| `Representation.Smooth.Contragredient.ExactProof` |
| `Representation.Smooth.Contragredient.GelfandKazhdanProof` |
| `Representation.Smooth.Contragredient.HomDualityProof` |
| `Representation.Smooth.Contragredient.InvariantPairingProof` |
| `Representation.Smooth.Factorization.TwoFactorExistenceProof` |
| `Representation.Smooth.Schur.Proof` |
| `Representation.Smooth.SmallRealizationProof` |
| `Representation.Tensor.ExternalMapSurjectivityProof` |
| `Representation.Tensor.SmoothDualInjectivityProof` |
| `Representation.Tensor.SmoothDualSurjectivityProof` |
| `Representation.Tensor.UnitaryProof` |
| `Representation.Twist.AdmissibilityProof` |
| `Representation.Twist.SubquotientProof` |
| `Representation.Unitary.CentralCharacterProof` |
| `Representation.Unitary.LeviCuspidalRealUnitarizationProof` |
| `Representation.Unitary.SquareIntegrableProof` |
| `Representation.Unitary.SupercuspidalRealUnitarizationProof` |
| `Representation.Unitary.UnitarizabilityContinuationProof` |
| `Representation.Unramified.SphericalConstituentExistenceProof` |
| `Representation.Whittaker.BruhatCellFactorizationProof` |
| `Representation.Whittaker.BruhatCellInvarianceProof` |
| `Representation.Whittaker.BruhatCellRestrictionVanishingProof` |
| `Representation.Whittaker.BruhatCellVanishingProof` |
| `Representation.Whittaker.BruhatCompatibleSupportProof` |
| `Representation.Whittaker.BruhatFiberCharacterCovarianceProof` |
| `Representation.Whittaker.BruhatHaarMeasureProof` |
| `Representation.Whittaker.BruhatOrbitalIntegrationProof` |
| `Representation.Whittaker.CompatibleMonomialFixedProof` |
| `Representation.Whittaker.DistributionInvarianceProof` |
| `Representation.Whittaker.GeneralizedCoefficientKernelProof` |
| `Representation.Whittaker.MultiplicityOneProof` |
| `Topology.GroupAction.FiniteOrbitProof` |
| `Weil.Representation.ContinuityProof` |
| `Weil.Representation.IsomorphismInvarianceProof` |
| `Weil.Representation.OperationClosureProof` |

The second table lists the 29 further closure modules that prove a named
Library proposition but are not the entry module of a published proof.
This includes every remaining closure module whose name ends in `Proof`. They
are early proof modules of the Library, or helper modules shipped
with a later proof. For some modules the table gives the statement that their
Markdown names, or the proof they help.

| Proved module | Statement or role |
| --- | --- |
| `Galois.FiniteField.ComparisonProof` | proves `FrobeniusComparison` (module `Galois.FiniteField.Comparison`); imported by `Weil.Local.Assembly` |
| `Galois.Local.SpectralProof` | `SpectralResidueExactness` |
| `Group.GL.Nonarchimedean` | statement module `Group.GL.NonarchimedeanStatement` (`ValuativeGeneralLinearNonarchimedean`) |
| `LocalField.Normalization.Proof` | `PadicNormalizationStatement` |
| `Representation.Compact.ProjectionProof` | |
| `Representation.Compact.SurjectivityProof` | |
| `Representation.CuspidalSupport.DeterminantUnitCornerStructureProof` | proves `DeterminantUnitCornerStructureStatement` (BZ76 Lemma 4.9); helper of `CuspidalSupport.CompactCoefficientFinitenessProof` |
| `Representation.CuspidalSupport.HarishChandraForwardProof` | helper of `CuspidalSupport.HarishChandraAssembly`; its theorems take the Cartan decomposition as a hypothesis, which the assembly discharges |
| `Representation.Jacquet.RefinedUpperCanonicalLiftProof` | helper of `Parabolic.NaturalJacquetDualityProof`; adds no statement |
| `Representation.Jacquet.StablePairingProof` | helper of `Parabolic.NaturalJacquetDualityProof`; adds no statement |
| `Representation.MatrixCoefficient.LawsProof` | |
| `Representation.Smooth.Admissibility.CofinalProof` | |
| `Representation.Smooth.Admissibility.EmbeddingProof` | `AdmissibleSubrepresentationStatement` |
| `Representation.Smooth.Admissibility.EquivalenceProof` | |
| `Representation.Smooth.Contragredient.CompactDualityProof` | statement `SmoothDualCompactFixedDualityStatement` |
| `Representation.Smooth.Contragredient.LawsProof` | |
| `Representation.Smooth.FixedVectors.LawsProof` | |
| `Representation.Smooth.FixedVectors.OrderProof` | |
| `Representation.Smooth.SmoothPart.BasicProof` | |
| `Representation.Smooth.Transfer.PullbackProof` | |
| `Representation.Smooth.Transfer.SubquotientProof` | |
| `Representation.Twist.AlgebraProof` | |
| `Representation.Twist.ContinuousCharacterProof` | `ContinuousComplexCharacterOpenKernel` |
| `Representation.Twist.DualProof` | |
| `Representation.Twist.PullbackProof` | |
| `Representation.Twist.SmoothProof` | `TwistSmoothCompatibility` |
| `Topology.CompactOpen.NeighborhoodBasis` | |
| `Weil.AlgebraicProof` | |
| `Weil.TopologyProof` | |

None of them is a proof of one of the later results listed above. To find these
modules, theorem declarations were scanned for types that are proposition
definitions of a `…Statement` module. The same scan finds only conditional
reductions besides the modules of the two tables: each of them proves a named
proposition from explicit theorem-valued hypotheses. They are
`Classification.NonadjacentLeibnizPieces`, `Classification.NonadjacentTwoBlock`,
`Classification.SegmentEdgeJacquetReduction`,
`Classification.SegmentFullJacquetEdgeData`,
`Classification.TwoSegmentShuffleAssembly`,
`Classification.TwoSupercuspidalAdjacentStructure`,
`CuspidalSupport.AssociatedConditional`,
`CuspidalSupport.CompactCoefficientFinitenessReduction`,
`Derivative.LeftMixedProductHigher`, `Derivative.LeftMixedProductVanishing`,
`Geometric.CosetOrbitOrdering`, `Parabolic.NaturalInductionDualityFromScalar`,
`Parabolic.SecondAdjointnessAssembly` and
`Smooth.Contragredient.GelfandKazhdanAssembly` (all under
`Representation.`). They are not proved inputs on their own. Wherever the
closure uses one of them, a proof module of the first table discharges its
hypotheses with published theorems. The present module discharges the only
hypothesis of `TwoSegmentShuffleAssembly` as described above.

## Development check

A Lean check over Library
commit `fcac121256163a8da6dd01a9483e1104a9b92aba` built this module with no
errors or warnings. Inspection of
`Langlands.Classification.twoSegmentSocleShuffleJacquet` reports a theorem with
level parameters `uF, uV, uW` and axioms `propext`, `Classical.choice` and
`Quot.sound`.
