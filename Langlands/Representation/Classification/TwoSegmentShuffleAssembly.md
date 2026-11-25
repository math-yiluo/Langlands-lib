# Assembly of the shuffle Jacquet filtration of two segment socles

Lean module: `Langlands.Representation.Classification.TwoSegmentShuffleAssembly`.
All declarations are in the namespace `Langlands.Classification.TwoSegmentShuffle`.

This is an internal supporting module for the proof of
`Langlands.Classification.TwoSegmentSocleShuffleJacquet`, which is completed in
`TwoSegmentSocleShuffleJacquetProof`. It does the
geometric-lemma bookkeeping of Zelevinsky 1980, 1.6 for `⟨Δ₀⟩ × ⟨Δ₁⟩`: it
deletes the zero pieces, indexes the remaining pieces by shuffle subsets and
counts composition factors. The identification of each remaining piece with its
shuffle tensor (the Ze80 3.1 step) is not proved here. It is the explicit
proposition `SurvivingPieceEquiv`. The module proves
`SurvivingPieceEquiv F T → TwoSegmentSocleShuffleJacquet F T`. It does not prove
`TwoSegmentSocleShuffleJacquet` unconditionally.

## Notation

Fix a prime `p`, a p-adic field `F` and compatible topological data `T`. For the
data of `TwoSegmentSocleShuffleJacquet`, write:

- `r = ρ.rank`;
- `C = BlockShape.uniform (m₀ + m₁) r ρ.rank_pos` for the uniform target shape;
- `d.shape` for the two-block source shape of `d.induced`, whose blocks carry the
  socles `d.blocks`.

`d.length = 2` is a hypothesis, not a definitional equality, so the two source
blocks are addressed as `Fin.cast h₂.symm 0` and `Fin.cast h₂.symm 1`. This is
the convention of the finite modules `UniformRefinementSurvivors` and
`UniformRefinementShuffleRealization`.

## Declarations

- `geometricPiece_subsingleton_of_not_dvd`. Let `d` be any segment-product datum
  with `d.HasSegmentSocles`, all of whose segments have rank `r`. Let `C` be any
  target shape and `w` any permutation, with standard intersection refinements
  `S` of `d.shape` and `R` of `C` (the source and target Levi equalities `hS`,
  `hR`). Suppose some piece of some `S j` has size not divisible by `r`. Then the
  actual geometric piece `(geometricPieceFunctor T d.shape C w S R hS hR).obj`
  evaluated at `⊗ⱼ d.blocks j` has subsingleton carrier.

  Proof: pick a block `j` and a piece `i` of `S j` with `¬ r ∣ (S j).size i`. The
  socle `d.blocks j` of segment `d.segments j` has rank `r`, so
  `IsSegmentSocle.jacquet_subsingleton_of_not_dvd` makes its normalized Jacquet
  module along `S j` zero. Then `SegmentEdge.refinedJacquet_external_subsingleton`
  makes the refined Jacquet module of the external tensor zero, and
  `SegmentEdge.geometricPiece_subsingleton` carries this through the remaining
  intersection transport and refined induction.

- `shuffleTensor_isIrreducible`. For an actual supercuspidal representative `A`
  of rank `r > 0`, any `m > 0`, any `S : Finset (Fin m)` and reals `a₀, a₁`, the
  external tensor `externalSmoothObject (shuffleFactors F T A.obj m hr S a₀ a₁)`
  is irreducible.

  Proof: block `i` of `shuffleFactors` is, by definition, the smooth object of the
  supercuspidal twist `SupercuspidalRep.twist (T.determinantPowerCharacter r e) … A`
  with `e = shuffleExponent S a₀ a₁ i`. So `glCuspidalTensor` applies to the
  uniform shape with these supercuspidal block factors and gives irreducibility.

- `card_shuffles`. The number of `S : Finset (Fin (m₀ + m₁))` with
  `S.card = m₀` is `(m₀ + m₁).choose m₀`. This is Mathlib's
  `Fintype.card_finset_len`.

- `shuffleJacquet_of_pieces`. Take `ρ`, `A`, `a₀`, `a₁`, `m₀`, `m₁` and `d` with
  `h₂ : d.length = 2` and `d.HasSegmentSocles`. Assume that both segments have
  rank `ρ.rank`, and the size equalities
  `h₀ : d.shape.size (Fin.cast h₂.symm 0) = m₀ * ρ.rank` and
  `h₁ : d.shape.size (Fin.cast h₂.symm 1) = m₁ * ρ.rank`. Assume the surviving
  piece hypothesis: for every `w : MinimalRepresentatives d.shape C`, standard
  intersection refinements `S`, `R` (full `IsIntersectionRefinement` data `hS`,
  `hR`) and `hdiv : ∀ j i, ρ.rank ∣ (S j).size i`, the geometric piece of `w`
  evaluated at `⊗ⱼ d.blocks j` is equivalent, as an actual representation of
  `C.Levi`, to the shuffle tensor
  `externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S' a₀ a₁)`
  of the subset `S' = (ShuffleRefinement.refinementShuffle … w.val S hS.2.1 w.property hdiv).val`.
  Then both clauses of `TwoSegmentSocleShuffleJacquet` hold for
  `J = CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj`.

- `SurvivingPieceEquiv F T` (Prop-valued internal definition, universes `uF uV`).
  It is the surviving piece hypothesis above, quantified over all data with
  exactly the binders and hypotheses of `TwoSegmentSocleShuffleJacquet`, in the
  same order. Those are `ρ`, `A`, `a₀`, `a₁`, `m₀`, `m₁`, `d`, `h₂`,
  `ρ.IsRepresentedBy A`, `d.HasSegmentSocles`, the two base equations and the two
  length equations. They are followed by `h₀`, `h₁`, `w`, `S`, `R`, `hS`, `hR`
  and `hdiv`. The size equalities `h₀`, `h₁` enter only as proof arguments of
  `refinementShuffle`.

- `segment_rank_eq`. If `d.length = 2` and the bases of the two segments are
  `ρ.twist a₀` and `ρ.twist a₁`, then every segment of `d` has rank `ρ.rank`.
  The twist does not change the rank (`CuspidalDatum.twist_rank` is `rfl`).

- `shape_size_cast`. Block `Fin.cast h₂.symm k` of `d.shape` has size
  `length * rank` of segment `k`. This holds by definition of `segmentShape`.

- `twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv`.
  `SurvivingPieceEquiv.{uF,uV} F T → TwoSegmentSocleShuffleJacquet.{uF,uV,uW} F T`,
  with independent universes `uF`, `uV`, `uW`. It derives the rank equalities with
  `segment_rank_eq` and `h₀`, `h₁` from the length equations, then applies
  `shuffleJacquet_of_pieces`.

## Proof of `shuffleJacquet_of_pieces`

1. Positivity. Block `Fin.cast h₂.symm 0` of `d.shape` has positive size
   `m₀ * ρ.rank`, so `m₀ > 0` and the total rank `(m₀ + m₁) * ρ.rank` is
   positive.
2. Geometric lemma. `Geometric.padicGeometricLemma.{uF, max uF uV}` at the total
   rank, for the source shape `d.shape` and the target shape `C`, gives
   refinement families `S`, `R` with their intersection equalities, an
   enumeration `enum : Fin M ≃ MinimalRepresentatives d.shape C` and a natural
   filtration of `jacquetInductionFunctor T d.shape C`. Its graded pieces are
   isomorphic to the geometric-piece functors of `enum i`. Evaluating at the
   external tensor `⊗ⱼ d.blocks j` (`CuspidalSupport.objectFiltrationAt`) gives an
   actual filtration of the representation
   `(jacquetInductionFunctor T d.shape C).obj (⊗ⱼ d.blocks j)`. This is
   definitionally `J = upperJacquet T C d.induced.obj`, since `d.induced` is the
   normalized product induction of `d.blocks` along `d.shape`.
3. Zero pieces. Let `P i` say that every piece of `S (enum i)` has size divisible
   by `ρ.rank`. If `¬ P i`, then `geometricPiece_subsingleton_of_not_dvd` makes
   the piece zero. Hence the graded quotient is zero too, through the equivalence
   from step 2.
4. Deletion. `ObjectRepFiltration.zeroFactorDeletionTheorem` deletes the indices
   with `¬ P i`. It gives a filtration `t` of `J` with `N` steps and
   `retained : Fin N ≃ {i // P i}`, with each graded quotient of `t` equivalent to
   the corresponding one of step 2.
5. Indexing. `enum` restricts to
   `{i // P i} ≃ ShuffleRefinement.DivisibleRefinementRepresentatives ρ.rank_pos d.shape S`.
   Composing with `ShuffleRefinement.divisibleEquivShuffles` gives
   `indexing : Fin N ≃ {S : Finset (Fin (m₀ + m₁)) // S.card = m₀}`.
   For a divisible representative `w`, `divisibleEquivShuffles` and
   `refinementShuffle` both apply `wholeTargetEquivShuffles` to the same minimal
   permutation. So the subset attached to `indexing k` is definitionally the
   `refinementShuffle` subset used in the surviving piece hypothesis.
6. Pieces. For each `k : Fin N`, compose three equivalences: graded quotient `k`
   of `t`, the graded quotient of the retained index, the geometric piece, and
   (by the hypothesis) the shuffle tensor of `indexing k`.
7. Counting. `finiteFamilyFiltrationMultiplicity` is applied to the finite family
   `S ↦ Rep.of (externalSmoothObject (shuffleFactors … S.val a₀ a₁)).representation`
   on `{S // S.card = m₀}`. The family is irreducible by
   `shuffleTensor_isIrreducible`. The result is a composition series of `J` of
   length `Nat.card {S // S.card = m₀} = (m₀ + m₁).choose m₀` (`card_shuffles`).
   For every `τ` in any universe `uW`, `HasJordanHolderMultiplicity J (Rep.of τ) m`
   holds iff `m` counts the subsets whose shuffle tensor is equivalent to `τ`.
   `Equiv.subtypeSubtypeEquivSubtypeInter` rewrites that count as the subtype
   `{S // S.card = m₀ ∧ Nonempty (… .Equiv τ)}` of the target statement.
   Irreducibility of `τ` is not used in this direction.

The theorem uses `set_option maxHeartbeats 1600000` because of the size of the
elaborated filtration terms. The same finite limit is used in
`SegmentEdgeJacquetReduction`.

## Scope

The module keeps arbitrary primes, finite p-adic fields, the supplied compatible
topology, arbitrary real `a₀, a₁` and natural `m₀, m₁`, repeated, equal and
linked segments, and the actual upper normalized induction and Jacquet modules.
The universes `uF`, `uV` and `uW` stay independent. The socles live in universe
`max uF uV`, and the geometric lemma is used at that universe. Nothing beyond
the statement's hypotheses and `SurvivingPieceEquiv` is assumed.

## Provenance

The provenance is internal. The argument is the bookkeeping part of Zelevinsky,
*Induced representations of reductive p-adic groups II* (Ann. Sci. ENS 1980),
§1.6 (printed pp. 171–172) applied to `⟨Δ₀⟩ × ⟨Δ₁⟩`, together with the
vanishing argument in the proof of Proposition 3.4 (printed p. 181). The source
is registered as `zelevinsky-1980-induced-ii`. The piece identification from
§3.1 is the hypothesis `SurvivingPieceEquiv`, not part of this module.

## Dependency audit

Proved inputs used directly:

| Input (module) | Use |
| --- | --- |
| `Geometric.padicGeometricLemma` (`Geometric.GeometricLemmaProof`) | The geometric-lemma filtration. |
| `ObjectRepFiltration.zeroFactorDeletionTheorem` (`Filtration.ZeroFactorDeletionProof`) | Deleting zero pieces. |
| `finiteFamilyFiltrationMultiplicity` (`Filtration.FiniteFamilyMultiplicityProof`) | Length and Jordan–Hölder multiplicities. |
| `CuspidalSupport.glCuspidalTensor` (`CuspidalSupport.CuspidalTensorProof`) | Irreducibility of the shuffle tensors. |
| `IsSegmentSocle.jacquet_subsingleton_of_not_dvd` (`Classification.UniformJacquetVanishing`) | Vanishing along shapes with a part not divisible by the rank. |
| `SegmentEdge.geometricPiece_subsingleton`, `SegmentEdge.refinedJacquet_external_subsingleton` (`Classification.SegmentEdgeJacquetReduction`) | Vanishing of a piece from vanishing of one factor's Jacquet module. Only these two lemmas are used; the conditional segment-edge filtration of that module is not. |
| `ShuffleRefinement.DivisibleRefinementRepresentatives`, `divisibleEquivShuffles` (`Classification.UniformRefinementSurvivors`) | Indexing the divisible representatives by shuffle subsets. |
| `ShuffleRefinement.refinementShuffle` (`Classification.UniformRefinementShuffleRealization`) | Only in the statement of `SurvivingPieceEquiv`. |
| `CuspidalSupport.objectFiltrationAt` (`CuspidalSupport.JacquetVanishingHelpers`) | Evaluating the functor filtration. |

The definitions `shuffleExponent`, `shuffleFactors`,
`TwoSegmentSocleShuffleJacquet` (module
`TwoSegmentSocleShuffleJacquetStatement`), `geometricPieceFunctor`,
`jacquetInductionFunctor`, `IsIntersectionRefinement`,
`CuspidalJacquetMultiplicity.upperJacquet` and `SupercuspidalRep.twist` are
used by name, as definitions. Mathlib supplies `Fintype.card_finset_len` and
`Equiv.subtypeSubtypeEquivSubtypeInter`.

The three modules `UniformJacquetVanishing`, `UniformRefinementSurvivors` and
`UniformRefinementShuffleRealization` listed above are finite-coordinate and
vanishing lemmas. Through their imports the closure also contains four further
finite modules: `UniformRefinementCombinatorics`, `UniformRefinementCoordinates`,
`UniformTargetBlockLabels` and `TwoSourceShuffleLabels`. These seven modules are
upstream inputs of the structure theorem
`JuxtaposedSegmentSocleReverseProductStructure`, not consequences of it.
Their own Markdown records their audits. None of them imports, assumes or proves
the juxtaposed or linked reverse-product structures or any other of the
conclusions listed below. They contain none of the declaration names listed below.

Transitive closure. The recursive project import closure of this module has
371 project modules besides itself. They are checked against Library commit
`7b0be54f6fdff0448d87d389ed9dc8b01c6f048f`. The closure contains no module whose
name or source mentions any of the following later conclusions, which this proof
does not use. That is checked by text search
for `JuxtaposedSegmentSocleReverseProductStructure`,
`LinkedSegmentSocleReverseProduct`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
`OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
`SegmentHeadProductIrreducibility`, `SquareIntegrableLanglandsClassification`
and `Derivative` over every source file of the closure. Its classification
modules are `ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`,
`Essential`, `LanglandsData`, `SegmentEdgeCombinatorics`,
`SegmentEdgeFactorHypotheses`, `SegmentEdgeJacquetReduction`,
`SegmentEdgeJacquetStatement`, `SegmentQuotientJacquetSingleBlock`, `Segments`,
`Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalSupport`,
`SupercuspidalTwist`, `Tempered`, `TwoSegmentSocleShuffleJacquetStatement`,
`TwoSourceShuffleLabels`, `TwoSupercuspidalProductStructureStatement`,
`UniformJacquetVanishing`, `UniformRefinementCombinatorics`,
`UniformRefinementCoordinates`, `UniformRefinementShuffleRealization`,
`UniformRefinementSurvivors` and `UniformTargetBlockLabels`. The statement module
`TwoSupercuspidalProductStructureStatement` comes in through
`SegmentEdgeFactorHypotheses`; it is a proposition definition only and is not
used as a hypothesis.

Proved-module inventory. The following table lists every module of the closure
that proves a named Library proposition. This covers all 81 closure modules
whose name ends in `Proof`. It also covers the nine other modules with a theorem
whose type is a named proposition. For `CuspidalSupport.JacquetVanishingHelpers`
these are only the rank-zero cases of the quasicuspidal and nonassociated
Jacquet-vanishing propositions. The remaining 281 closure modules contain only
definitions, proposition definitions and supporting lemmas about particular
objects. None of them proves a named proposition outright; two of them are the
conditional reductions described after the table. Module names omit the
prefix `Langlands.`. For two modules the table names the statement that their
Markdown names.

| Proved module | Note |
| --- | --- |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` | |
| `Analysis.Local.QuotientAutomorphismProof` | |
| `Analysis.Local.QuotientAveragingKernel` | |
| `Analysis.Local.QuotientMeasureExistence` | |
| `Analysis.Local.QuotientPositiveLifting` | |
| `Group.GL.BlockModulusHaarProof` | |
| `Group.GL.BlockUnipotentHaarProof` | |
| `Group.GL.CountabilityProof` | |
| `Group.GL.Nonarchimedean` | statement module `Group.GL.NonarchimedeanStatement` |
| `Group.GL.UpperBruhatPivotProof` | |
| `Group.GL.UpperBruhatProof` | |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` | |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` | |
| `HarmonicAnalysis.TriangularTranslationProof` | |
| `LocalField.Normalization.Proof` | |
| `Representation.Compact.ProjectionProof` | |
| `Representation.Compact.SurjectivityProof` | |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` | |
| `Representation.CuspidalSupport.AssociationLawsProof` | |
| `Representation.CuspidalSupport.CuspidalTensorProof` | |
| `Representation.CuspidalSupport.JacquetSubquotientProof` | |
| `Representation.CuspidalSupport.JacquetVanishingHelpers` | rank-zero cases only |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` | |
| `Representation.CuspidalSupport.MinimalJacquetProof` | |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` | |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` | |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` | |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` | |
| `Representation.Filtration.GradedRefinementProof` | |
| `Representation.Filtration.IntervalLiftProof` | |
| `Representation.Filtration.IrreducibleMultiplicityProof` | |
| `Representation.Filtration.JordanHolderComparisonProof` | |
| `Representation.Filtration.JordanHolderTransportProof` | |
| `Representation.Filtration.LengthCriterionProof` | |
| `Representation.Filtration.LengthTwoMatching` | |
| `Representation.Filtration.MultiplicityIndependenceProof` | |
| `Representation.Filtration.SubsingletonProof` | |
| `Representation.Filtration.ZeroFactorDeletionProof` | |
| `Representation.Geometric.BlockSixDecomposableProof` | |
| `Representation.Geometric.BruhatMatrixExistenceProof` | |
| `Representation.Geometric.BruhatWeylReflectionProof` | |
| `Representation.Geometric.ClosedSubgroupMackeyProof` | |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` | |
| `Representation.Geometric.GeometricLemmaProof` | |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | |
| `Representation.Geometric.MonotoneBlocksProof` | |
| `Representation.Geometric.OrbitSectionExtensionProof` | |
| `Representation.Geometric.PadicCorrectionCancellationProof` | |
| `Representation.Geometric.PadicParabolicBruhatProof` | |
| `Representation.Geometric.ParabolicOrbitJacquetProof` | |
| `Representation.Geometric.ParabolicSupportGradedProof` | |
| `Representation.Geometric.ParabolicSupportJacquetProof` | |
| `Representation.Geometric.StandardIntersectionsProof` | |
| `Representation.Geometric.WeylMinimalRepresentativeProof` | |
| `Representation.Geometric.WeylUniquenessProof` | |
| `Representation.Induction.CharacterTwistProof` | |
| `Representation.Induction.CompactAutomorphismIntegralProof` | |
| `Representation.Induction.CompactCoinvariantBijectivityProof` | |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` | |
| `Representation.Induction.CompactLocalSectionSpanningProof` | |
| `Representation.Induction.CompactQuotientProof` | |
| `Representation.Induction.CompactSurjectivityProof` | |
| `Representation.Induction.CompactTransitivityProof` | |
| `Representation.Induction.NormalCoinvariantKernelProof` | |
| `Representation.Induction.NormalCoinvariantProof` | |
| `Representation.Induction.SplitQuotientProof` | |
| `Representation.Induction.SurjectivityProof` | |
| `Representation.Jacquet.ExactProof` | |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` | |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` | |
| `Representation.Parabolic.QuotientCompactProof` | |
| `Representation.Parabolic.UnipotentFiniteContainment` | |
| `Representation.RankinSelberg.UnipotentUnimodularity` | |
| `Representation.Smooth.Admissibility.CofinalProof` | |
| `Representation.Smooth.Admissibility.EquivalenceProof` | |
| `Representation.Smooth.Contragredient.CompactDualityProof` | statement `SmoothDualCompactFixedDualityStatement` |
| `Representation.Smooth.Contragredient.LawsProof` | |
| `Representation.Smooth.Schur.Proof` | |
| `Representation.Smooth.SmallRealizationProof` | |
| `Representation.Smooth.SmoothPart.BasicProof` | |
| `Representation.Smooth.Transfer.PullbackProof` | |
| `Representation.Smooth.Transfer.SubquotientProof` | |
| `Representation.Twist.AdmissibilityProof` | |
| `Representation.Twist.AlgebraProof` | |
| `Representation.Twist.SmoothProof` | |
| `Representation.Twist.SubquotientProof` | |
| `Topology.CompactOpen.NeighborhoodBasis` | |
| `Topology.GroupAction.FiniteOrbitProof` | |
| `Weil.Representation.ContinuityProof` | |
| `Weil.Representation.IsomorphismInvarianceProof` | |

Two closure modules are conditional reductions and are not proved inputs.
`Geometric.CosetOrbitOrdering` reduces `ClosedSubgroupOrbitOrdering`
to `Topology.FiniteOrbitOrdering`. `Geometric.GeometricLemmaProof` discharges
that hypothesis with `Topology.finiteOrbitOrdering` from
`Topology.GroupAction.FiniteOrbitProof`, which is listed above.
`Classification.SegmentEdgeJacquetReduction` is the direct input described
above; only its two vanishing lemmas are used.

None of the modules in the two tables above is a proof of one of the later
conclusions listed above. The closure uses no derivative
construction or theorem, and no special-head or socle product criterion.

## Development check

A Lean check over Library
commit `7b0be54f6fdff0448d87d389ed9dc8b01c6f048f` compiled the module with no
errors or warnings.
