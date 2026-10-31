# Assembly of the shuffle Jacquet filtration of two segment socles

Author: Worker 1145.

Lean module: `Langlands.Representation.Classification.TwoSegmentShuffleAssembly`.
All declarations are in the namespace `Langlands.Classification.TwoSegmentShuffle`.

This is an internal supporting unit for the proof task
`343ddfde-e74c-46b8-a559-0c8f3a3145a6`, which proves
`Langlands.Classification.TwoSegmentSocleShuffleJacquet`. It does the
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

Proved inputs used directly, with the tasks that produced them:

| Input (module) | Artifact / task | Use |
| --- | --- | --- |
| `Geometric.padicGeometricLemma` (`Geometric.GeometricLemmaProof`) | proof `f606bb75-3194-405e-ba6a-1edb4294d539`, task `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` | The geometric-lemma filtration. |
| `ObjectRepFiltration.zeroFactorDeletionTheorem` (`Filtration.ZeroFactorDeletionProof`) | proof `2813cc17-8241-4b38-b9f6-da8e3af69fe2`, task `e0f6a21c-44dd-4676-ad49-1656e49573ed` | Deleting zero pieces. |
| `finiteFamilyFiltrationMultiplicity` (`Filtration.FiniteFamilyMultiplicityProof`) | proof `3e121bcb-afe6-453d-b01e-2043e91c4b58`, task `c9dbd607-82e5-4821-b367-736e876565d9` | Length and Jordan–Hölder multiplicities. |
| `CuspidalSupport.glCuspidalTensor` (`CuspidalSupport.CuspidalTensorProof`) | proof `8513f998-61e8-49e4-b1a5-738e4315b437`, task `cece816e-aee9-40ca-9139-d770491b6178` | Irreducibility of the shuffle tensors. |
| `IsSegmentSocle.jacquet_subsingleton_of_not_dvd` (`Classification.UniformJacquetVanishing`) | supporting unit `7474c907-7494-4934-927c-a643fa565c6e` (Worker 167), filed under task `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | Vanishing along shapes with a part not divisible by the rank. |
| `SegmentEdge.geometricPiece_subsingleton`, `SegmentEdge.refinedJacquet_external_subsingleton` (`Classification.SegmentEdgeJacquetReduction`) | supporting unit `936ff465-c0b4-4e1f-8c8a-ef6139f08699` (Worker 890), filed under task `b331611c-526d-4925-87fe-ea67ed6e6fed` | Vanishing of a piece from vanishing of one factor's Jacquet module. Only these two lemmas are used; the conditional segment-edge filtration of that module is not. |
| `ShuffleRefinement.DivisibleRefinementRepresentatives`, `divisibleEquivShuffles` (`Classification.UniformRefinementSurvivors`) | supporting unit `e4622c15-8740-414c-aa94-7f4be9a0e3b5` (Worker 167), task `0c90f7e4-…` | Indexing the divisible representatives by shuffle subsets. |
| `ShuffleRefinement.refinementShuffle` (`Classification.UniformRefinementShuffleRealization`) | supporting unit `ceacade2-81f9-43a6-b367-e690e79a271d` (Worker 167), task `0c90f7e4-…` | Only in the statement of `SurvivingPieceEquiv`. |
| `CuspidalSupport.objectFiltrationAt` (`CuspidalSupport.JacquetVanishingHelpers`) | supporting unit `42536722-fde0-468f-b133-c8c3e83f47a3`, task `b17b8c8c-858b-4b48-994b-e3641cb05f02` | Evaluating the functor filtration. |

The definitions `shuffleExponent`, `shuffleFactors`,
`TwoSegmentSocleShuffleJacquet` (statement artifact
`2081c976-7739-449f-a369-4f1aad69176f`, task
`efe00a4a-423f-449a-acf6-4e7e0eaf7f35`), `geometricPieceFunctor`,
`jacquetInductionFunctor`, `IsIntersectionRefinement`,
`CuspidalJacquetMultiplicity.upperJacquet` and `SupercuspidalRep.twist` are
used by name, as definitions. Mathlib supplies `Fintype.card_finset_len` and
`Equiv.subtypeSubtypeEquivSubtypeInter`.

The three supporting units of Worker 167 listed above are finite-coordinate and
vanishing lemmas. Through their imports the closure also contains four further
finite units of Worker 167: `UniformRefinementCombinatorics`
(`18231764-fb7e-402c-9890-bd825da3af72`), `UniformRefinementCoordinates`
(`a5dd707e-d6ca-482f-b2f4-6c1dface8877`), `UniformTargetBlockLabels`
(`c4f50f7f-3046-449f-9528-8a51ad911304`) and `TwoSourceShuffleLabels`
(`6324c466-f187-49e5-ba73-cbf7b5a12a89`). These seven units were filed under the
excluded task `0c90f7e4-…` (`JuxtaposedSegmentSocleReverseProductStructure`),
but they are upstream inputs of that structure theorem, not consequences of it.
Their own Markdown records their audits. None of them imports, assumes or proves
the juxtaposed or linked reverse-product structures or any other excluded
conclusion. They contain no excluded declaration name.

Transitive closure. The recursive project import closure of this module has
371 project modules besides itself. They are checked against Library commit
`7b0be54f6fdff0448d87d389ed9dc8b01c6f048f`. The closure contains no module whose
name or source mentions any excluded declaration. That is checked by text search
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

A second text search looked for the 21 task identifiers named in the exclusions
of task `343ddfde-e74c-46b8-a559-0c8f3a3145a6`, over every Lean and Markdown
file of the closure. It finds only two kinds of hits. The Markdown of Worker
167's units records their filing under `0c90f7e4-…`, as explained above.
`Parabolic.RefinedJacquetTensor.md` lists several excluded tasks in its own
audit table, which records each of them as absent from its closure.

Proved-module inventory. The following table lists every module of the closure
that proves a named Library proposition. This covers all 81 closure modules
whose name ends in `Proof`. It also covers the nine other modules with a theorem
whose type is a named proposition. For `CuspidalSupport.JacquetVanishingHelpers`
these are only the rank-zero cases of the quasicuspidal and nonassociated
Jacquet-vanishing propositions. The remaining 281 closure modules contain only
definitions, proposition definitions and supporting lemmas about particular
objects. None of them proves a named proposition outright; two of them are the
conditional reductions described after the table. Module names omit the
prefix `Langlands.`. "Historical" marks a module from the project's first proof
rounds. Such a module has no proof task in the current task registry, so the
table gives the published statement that its Markdown names.

| Proved module | Originating task or provenance |
| --- | --- |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` | task `071e4d23-2827-49e3-953a-b755c243d302` |
| `Analysis.Local.QuotientAutomorphismProof` | task `88e8f6c0-c9cf-40fb-90e5-2ddbb72cc479` |
| `Analysis.Local.QuotientAveragingKernel` | task `4ecaafca-57e4-472e-9501-7cf362d21007` |
| `Analysis.Local.QuotientMeasureExistence` | task `7d14a606-bb49-4cf0-9f89-8034e21e9f15` |
| `Analysis.Local.QuotientPositiveLifting` | task `40466063-2de2-456b-ae79-93c782b76e0b` |
| `Group.GL.BlockModulusHaarProof` | task `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.BlockUnipotentHaarProof` | task `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.CountabilityProof` | task `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Group.GL.Nonarchimedean` | historical; statement module `Group.GL.NonarchimedeanStatement` |
| `Group.GL.UpperBruhatPivotProof` | task `cb1e92a3-bf5e-4765-a993-c41522dd0022` |
| `Group.GL.UpperBruhatProof` | task `8c2f6593-d22c-44b1-be0b-4ad6cb08445f` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` | task `0e28951e-9779-4567-b8b0-c95334854fac` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` | task `574c1368-49a7-48eb-a084-18006b0f2871` |
| `HarmonicAnalysis.TriangularTranslationProof` | task `7f443547-d49c-4edd-ba7e-9f0fb9d6ad67` |
| `LocalField.Normalization.Proof` | historical; statement artifact `62e8bb5c-3f54-449e-bbd6-98de9dc15781` |
| `Representation.Compact.ProjectionProof` | task `849a1dbe-68d3-4bc8-9c67-ca059539e827` |
| `Representation.Compact.SurjectivityProof` | historical; statement artifact `40e87eae-9077-41b0-a7d0-49e3f58c1d41` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` | task `17247e03-9471-4f13-81fa-e4f7058619a0` |
| `Representation.CuspidalSupport.AssociationLawsProof` | task `944b9b06-1e87-42d1-a565-00395593eb8b` |
| `Representation.CuspidalSupport.CuspidalTensorProof` | task `cece816e-aee9-40ca-9139-d770491b6178` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` | task `b605839f-d645-4427-892a-04dd871b7c49` |
| `Representation.CuspidalSupport.JacquetVanishingHelpers` | supporting unit `42536722-fde0-468f-b133-c8c3e83f47a3`, task `b17b8c8c-858b-4b48-994b-e3641cb05f02`; rank-zero cases only |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` | task `d042dc77-fd25-4c92-b943-d456ffd86fe9` |
| `Representation.CuspidalSupport.MinimalJacquetProof` | task `f28607f5-1eef-4329-ae18-2576ef25ab6a` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` | task `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` | task `b17b8c8c-858b-4b48-994b-e3641cb05f02` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` | task `5becc159-1242-4fa4-9102-79aa6e2726c0` |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` | task `c9dbd607-82e5-4821-b367-736e876565d9` |
| `Representation.Filtration.GradedRefinementProof` | task `8f135e79-b688-4075-b8e6-b05a81a36883` |
| `Representation.Filtration.IntervalLiftProof` | task `58e0544d-0db2-42f5-8d39-79d38ff5e2cd` |
| `Representation.Filtration.IrreducibleMultiplicityProof` | task `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.JordanHolderComparisonProof` | task `b43fcaf9-8be5-4717-a87b-a84c667efcbe` |
| `Representation.Filtration.JordanHolderTransportProof` | task `77ffbd6e-17db-4751-8dee-c6dcb3b92e09` |
| `Representation.Filtration.LengthCriterionProof` | task `8520a63d-88a5-45e7-adef-84849528ad9d` |
| `Representation.Filtration.LengthTwoMatching` | task `53969569-6b54-45b3-a1f8-89f1fe96a1f8` |
| `Representation.Filtration.MultiplicityIndependenceProof` | task `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.SubsingletonProof` | task `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` |
| `Representation.Filtration.ZeroFactorDeletionProof` | task `e0f6a21c-44dd-4676-ad49-1656e49573ed` |
| `Representation.Geometric.BlockSixDecomposableProof` | task `91670dc7-3166-4d54-b9cb-bcb148f080b5` |
| `Representation.Geometric.BruhatMatrixExistenceProof` | task `f22fde8e-f597-44d0-a53d-290de4c59b2d` |
| `Representation.Geometric.BruhatWeylReflectionProof` | task `4ff454dd-caa9-435d-8c9b-bc4ed0d4b415` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` | task `e71f23b6-a9d9-4bc4-9af9-cde7a187ff8b` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` | task `9c98daee-a78a-429a-81dc-4cebbe02dee1` |
| `Representation.Geometric.GeometricLemmaProof` | task `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | task `1a585c66-e21e-4071-84a0-09a32af9d745` |
| `Representation.Geometric.MonotoneBlocksProof` | task `a5db9be0-3f71-4528-89a8-cd92a0c5e411` |
| `Representation.Geometric.OrbitSectionExtensionProof` | task `58ca13a3-4bf3-4aaa-8b7d-e8156d189c64` |
| `Representation.Geometric.PadicCorrectionCancellationProof` | task `7e7f9c7b-a0fb-4b6a-9539-2d6b9988a4cc` |
| `Representation.Geometric.PadicParabolicBruhatProof` | task `b2c9fb09-d2c7-4895-8320-b447e3cc98c6` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` | task `18915f54-27ba-4ed6-a6ba-44d2590fd858` |
| `Representation.Geometric.ParabolicSupportGradedProof` | task `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.ParabolicSupportJacquetProof` | task `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.StandardIntersectionsProof` | task `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` | task `6e35399b-9029-438e-9663-5ce96ab02576` |
| `Representation.Geometric.WeylUniquenessProof` | task `9ad51693-f8a1-45de-949a-72d07ecc13b9` |
| `Representation.Induction.CharacterTwistProof` | task `fb3e71c3-36c9-4f69-bc65-3572eba2c084` |
| `Representation.Induction.CompactAutomorphismIntegralProof` | task `322d05be-f0c4-46f3-a5ce-0bb0a724e68f` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` | task `cbaf9d61-f090-41e3-8269-9ae5a6992693` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` | task `9f55d4f4-ce37-42fa-881d-413bffce13e2` |
| `Representation.Induction.CompactLocalSectionSpanningProof` | task `0dbbc4e6-1b6c-4682-9e94-bf4b9aa04614` |
| `Representation.Induction.CompactQuotientProof` | task `672038be-3175-4fbd-85a6-d8c272aa63ec` |
| `Representation.Induction.CompactSurjectivityProof` | task `a757e2b6-b764-46f5-8f53-57f3d2d80f9b` |
| `Representation.Induction.CompactTransitivityProof` | task `84a052cc-bc16-4936-b3c5-0e50f92ff0a8` |
| `Representation.Induction.NormalCoinvariantKernelProof` | task `89c9c2dc-a112-4cae-b148-3e6de8be0583` |
| `Representation.Induction.NormalCoinvariantProof` | task `ffe24f57-d375-48bf-b0ef-536f8cea58dd` |
| `Representation.Induction.SplitQuotientProof` | task `75bc696d-7093-45b4-b951-e84ca3cd5f79` |
| `Representation.Induction.SurjectivityProof` | task `63c695c6-3dbd-46f6-b675-f46f1aa2a0bb` |
| `Representation.Jacquet.ExactProof` | task `d30fdbfc-1ea3-4554-9b0f-540abe813aea` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` | task `4c32a273-8e38-4a7c-abb9-f1ad5075ecb9` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` | task `9d580fe5-0589-4dfa-9506-1010e413a529` |
| `Representation.Parabolic.QuotientCompactProof` | task `400d2277-4574-4aea-a50c-da70cb1702f2` |
| `Representation.Parabolic.UnipotentFiniteContainment` | task `cba1f5ba-df9a-4ee7-a403-baaeebbf4d63` |
| `Representation.RankinSelberg.UnipotentUnimodularity` | task `4ad92be9-9115-4e7d-b42a-b2adc7dde3e5` |
| `Representation.Smooth.Admissibility.CofinalProof` | historical; statement artifact `accbe6c3-27d4-43d9-a227-65c4e7b6a993` |
| `Representation.Smooth.Admissibility.EquivalenceProof` | historical; statement artifact `b844a6ce-e7d4-4e71-8bd3-8a80abb57ba0` |
| `Representation.Smooth.Contragredient.CompactDualityProof` | historical; statement `SmoothDualCompactFixedDualityStatement` |
| `Representation.Smooth.Contragredient.LawsProof` | historical; statement artifact `ff1e06de-a5b0-4bc7-81b5-8b4555029cef` |
| `Representation.Smooth.Schur.Proof` | task `7418b301-258f-4839-83ff-8b508b8a9abd` |
| `Representation.Smooth.SmallRealizationProof` | task `baca19e0-4b51-4368-9b1a-817f6d583c5f` |
| `Representation.Smooth.SmoothPart.BasicProof` | historical; statement artifact `7101568f-3e71-4b9d-b1c5-f35546e0e8dd` |
| `Representation.Smooth.Transfer.PullbackProof` | task `442dfa1c-e218-4bd4-b7c0-faaccfcf26e7` |
| `Representation.Smooth.Transfer.SubquotientProof` | task `0975ce00-a7a0-4031-a31f-1df98f3afaf3` |
| `Representation.Twist.AdmissibilityProof` | task `481101cd-15e1-460d-84f8-3bc4331be8b6` |
| `Representation.Twist.AlgebraProof` | historical; statement artifact `2fbcd8fa-9374-4793-bf3b-f0e5a4fbb3d7` |
| `Representation.Twist.SmoothProof` | historical; statement artifact `f3828b8f-ac55-4352-955b-9dc9787da742` |
| `Representation.Twist.SubquotientProof` | task `84b8a0ef-a7b9-4ed9-ab40-1b430d7e0f86` |
| `Topology.CompactOpen.NeighborhoodBasis` | task `83c9e2e3-7d24-4ae8-ba36-8fda72b4f789` |
| `Topology.GroupAction.FiniteOrbitProof` | task `72152240-c606-4fc3-87a0-e6d5972c32fa` |
| `Weil.Representation.ContinuityProof` | task `8d52aad7-9f5b-41c1-bf76-c1e6483b9639` |
| `Weil.Representation.IsomorphismInvarianceProof` | task `53bd2d23-f25a-4747-9ac9-f82617e20070` |

Two closure modules are conditional reductions and are not proved inputs.
`Geometric.CosetOrbitOrdering` (supporting unit
`a8dc116e-9481-4d5c-b25f-9e0bf5efb0dc`, task
`637ff3d3-b8ef-49e8-9ef3-afec188e07e9`) reduces `ClosedSubgroupOrbitOrdering`
to `Topology.FiniteOrbitOrdering`. `Geometric.GeometricLemmaProof` discharges
that hypothesis with `Topology.finiteOrbitOrdering` from
`Topology.GroupAction.FiniteOrbitProof`, which is listed above.
`Classification.SegmentEdgeJacquetReduction` is the direct input described
above; only its two vanishing lemmas are used.

Apart from the filing of Worker 167's units under `0c90f7e4-…`, explained
above, none of the tasks in the two tables above is among the exclusions of
task `343ddfde-e74c-46b8-a559-0c8f3a3145a6`. The closure uses no derivative
construction or theorem, and no special-head or socle product criterion.

## Development check

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library
commit `7b0be54f6fdff0448d87d389ed9dc8b01c6f048f` compiled the module with no
errors or warnings.
