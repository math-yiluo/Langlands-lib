# Jacquet vanishing from block divisibility

Author: Worker 167.

This internal adapter proves vanishing of actual normalized Jacquet modules
along any target shape with a block not divisible by a common divisor of the
source block sizes. It specializes the published quasicuspidal Jacquet
vanishing theorem, transfers the result to actual smooth subquotients, and
applies it to segment subrepresentations and socles. It supplies a zero-piece
criterion for the juxtaposed-segment argument, not the shuffle Jacquet formula
or the parent reverse-product structure.

`Classification.NondivisibleJacquetVanishing T r π` is the reusable
Prop-valued predicate that, for every block shape `D` of the degree of `π`,
the existence of a block whose size is not divisible by `r` implies that
the actual normalized Jacquet carrier of `π` along `D` is subsingleton.
The closing theorem `IsSegmentSocle.nondivisibleJacquetVanishing` proves
this predicate at the given segment's cuspidal rank. It packages the
per-shape theorem without an additional hypothesis.

## Finite obstruction

For arbitrary natural numbers `n,r`, shapes `B,D : BlockShape n`, and any
standard refinement `S` of `D`, suppose permutation-matrix conjugation by `w`
maps the actual source Levi onto the Levi of `D.flatten S`. If `r` divides
every `B.size i`, `dvd_target_size_of_conjugatesLevi_flatten` proves that it
divides every `D.size j`.

The published block map is surjective and preserves block sizes, so each
inner block of `S j` has the size of a source block. The flattening size
identity makes this an equality of the actual sizes. Summing over those inner
blocks gives `D.size j`, and divisibility is closed under finite sums.
No block-count bound, uniformity, positivity of `r`, or minimality of `w` is
needed for this finite statement.

`no_associated_refinement_of_not_dvd` takes the contrapositive. The published
identification of the embedded refined Levi with the flattened Levi rewrites
the subgroup equality in the no-association condition. A target block not
divisible by `r` contradicts the preceding result.

## Actual vanishing and subquotients

`jacquet_induction_subsingleton_of_not_dvd` applies the published unconditional
`quasicuspidalJacquetVanishing` to this obstruction. For any smooth
quasicuspidal representation of the actual source Levi, its normalized
parabolic induction has a subsingleton normalized Jacquet carrier along `D`.
This is an actual zero representation, not a statement about a
Grothendieck class.

`subquotient_jacquet_subsingleton_of_not_dvd` applies the published exact
normalized Jacquet subquotient theorem. The Jacquet module of a given actual
smooth subquotient is a subquotient of the zero module, so its carrier is
subsingleton. `supercuspidal_product_subquotient_jacquet_subsingleton_of_not_dvd`
uses the published external tensor cuspidality theorem for actual
supercuspidal block factors; its total source rank is assumed positive.

`segment_induction_subquotient_jacquet_subsingleton_of_not_dvd` specializes
to the uniform shape with `m` blocks of size `r`, with `m,r > 0`.
The actual inducing factors are the determinant-power twists of a given
supercuspidal object. The existing supercuspidal twist construction has exactly
the segment-factor smooth objects, so the resulting product induction is the
published increasing segment induction.

The segment subrepresentation and socle theorems use an actual injective intertwiner from the given
segment subrepresentation or socle into its increasing induction. This is an
actual subquotient, so the preceding result proves its normalized Jacquet
module along every shape having a block not divisible by the segment rank
is zero. No existence or uniqueness theorem for segment socles is assumed.
The field and representation-carrier universes remain independent.
The final theorem introduces an arbitrary target shape and applies this
socle result to prove `NondivisibleJacquetVanishing`.

## Provenance and dependency audit

All new deductions are internal consequences of published finite-coordinate,
vanishing, tensor, twist and exactness results. No external source is claimed
for this adapter. The mathematical inputs are imported by their current Lean
names. The following table identifies the results used directly and their
originating tasks.

| Published input | Task | Use here |
| --- | --- | --- |
| `TotalConjugatingCount.blockMap_surjective`, `TotalConjugatingCount.size_blockMap` | `5becc159-1242-4fa4-9102-79aa6e2726c0` | Every flattened target block has the size of a source block. |
| `BlockShape.flattenBlockEquiv`, `BlockShape.flatten_size_flattenBlockEquiv` in `CuspidalSupport.MinimalJacquetProof` | `f28607f5-1eef-4329-ae18-2576ef25ab6a` | Identify the inner refinement sizes before summation. |
| `SegmentEdge.refinedLevi_map_eq_flatten_leviSubgroup` | `b331611c-526d-4925-87fe-ea67ed6e6fed` | Rewrite the actual embedded refined-Levi subgroup. |
| `CuspidalSupport.quasicuspidalJacquetVanishing` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` | Convert the finite obstruction to actual Jacquet vanishing. |
| `CuspidalSupport.subsingleton_of_isSubquotient` in `JacquetVanishingHelpers` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` | A subquotient of the zero module has zero carrier. |
| `CuspidalSupport.normalizedJacquetSubquotient` | `b605839f-d645-4427-892a-04dd871b7c49`, revision 2 | Transport an actual smooth subquotient through normalized Jacquet descent. |
| `CuspidalSupport.glCuspidalTensor` | `cece816e-aee9-40ca-9139-d770491b6178` | Supply quasicuspidality of the actual external tensor product. |
| `GeneralLinear.SupercuspidalRep.twist` and the determinant-power character lemmas in `Classification.SupercuspidalTwist` | `a7a453ca-879b-4dd7-a07e-bfe49c8e791c` | Package each actual increasing-segment factor as a supercuspidal object. |
| `SmoothRep.IsSubrepresentation.isSubquotient` in `Classification.SupercuspidalSupport` | `a7a453ca-879b-4dd7-a07e-bfe49c8e791c` | Use the given injective segment intertwiner as an actual subquotient. |
| The segment definitions and `IsSegmentSocle.isSegmentSubrepresentation` in `Classification.Segments` | `a7a453ca-879b-4dd7-a07e-bfe49c8e791c` | Extract the increasing-induction injection from the given segment predicate. |

Only the first subgroup equality from `SegmentEdgeFactorHypotheses` is used.
Its other conditional factor formulas and the propositions in
`TwoSupercuspidalProductStructureStatement` are not proved inputs here.
Likewise, the segment predicates supply a given injection; no segment
existence, uniqueness, support uniqueness, or segment Jacquet formula is
inferred from a proposition definition.

The complete recursive project import closure was checked against Library
commit `47d510a700120ee55273befb9e9cfbff513b1eb4`. It consists of 323
imported project modules. Every imported Lean/Markdown pair matches that
Library byte for byte; every module has its companion Markdown. The source
import graph and executable Lean declarations contain no excluded conclusion.
The exact-proof inputs in that closure are inventoried below, with their
originating tasks. Their independent acceptance, successful machine validation
and publication were checked in the published archive. The remaining modules
supply infrastructure, supporting internal lemmas and proposition definitions.
Mathlib supplies finite-sum divisibility and the ordinary algebraic and finite
type infrastructure.

In particular, the imported unconditional geometric lemma is
`Geometric.padicGeometricLemma`, from task
`67ebcf61-3d58-4499-9c0c-c847e90aaeb4`. It is an actual finite-filtration
theorem, rather than that task's separate countability theorem.
Its geometric, Haar-measure, compact-support, exactness and Weyl prerequisites
remain upstream of segment classification. The vanishing proof uses that
filtration and quasicuspidality. The subquotient proof uses actual unipotent
coinvariant exactness. The tensor proof uses Schur's lemma and elementary
external-tensor properties. The finite block map uses permutation-matrix
conjugation. The twist proof uses determinant characters and coinvariants.
These routes give no dependency on the excluded classification results.

The audit preserves the full independence requirements of the parent task:
no linked reverse-product structure or its quotient-homomorphism successor;
no linked-pair reducibility or segment-socle product criterion; no adjacent
unlinked socle swap, two-segment socle commutation, linked socle gluing or their
proof successors; no ordered multisegment socle existence, socle exhaustion,
segment analytic classification, special-head multisegment exhaustion,
ordered special-head existence, quotient coverage or tempered-block uniqueness;
no square-integrable Langlands classification, square-integrable exhaustion
or regular exhaustion; and no `SegmentHeadProductIrreducibility` or its
conclusions. No derivative construction or derivative theorem occurs in the
closure. These exclusions apply transitively, not just to the three direct
imports. None of the originating proof tasks below is one of the excluded
tasks.

This unit proves only the stated finite obstruction and its actual
Jacquet-vanishing consequences. It supplies neither a nonvanishing criterion
for divisible shapes nor the remaining exact inputs to
`JuxtaposedSegmentSocleReverseProductStructure`.

### Imported exact-proof inventory

Module names in the following table omit the common `Langlands.` prefix.
The task column records provenance; the Lean imports use module names alone.

| Imported proved module | Originating task |
| --- | --- |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` | `071e4d23-2827-49e3-953a-b755c243d302` |
| `Analysis.Local.QuotientAutomorphismProof` | `88e8f6c0-c9cf-40fb-90e5-2ddbb72cc479` |
| `Analysis.Local.QuotientAveragingKernel` | `4ecaafca-57e4-472e-9501-7cf362d21007` |
| `Analysis.Local.QuotientMeasureExistence` | `7d14a606-bb49-4cf0-9f89-8034e21e9f15` |
| `Analysis.Local.QuotientPositiveLifting` | `40466063-2de2-456b-ae79-93c782b76e0b` |
| `Group.GL.BlockModulusHaarProof` | `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.BlockUnipotentHaarProof` | `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.CountabilityProof` | `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Group.GL.UpperBruhatPivotProof` | `cb1e92a3-bf5e-4765-a993-c41522dd0022` |
| `Group.GL.UpperBruhatProof` | `8c2f6593-d22c-44b1-be0b-4ad6cb08445f` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` | `0e28951e-9779-4567-b8b0-c95334854fac` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` | `574c1368-49a7-48eb-a084-18006b0f2871` |
| `HarmonicAnalysis.TriangularTranslationProof` | `7f443547-d49c-4edd-ba7e-9f0fb9d6ad67` |
| `Representation.CuspidalSupport.AssociationLawsProof` | `944b9b06-1e87-42d1-a565-00395593eb8b` |
| `Representation.CuspidalSupport.CuspidalTensorProof` | `cece816e-aee9-40ca-9139-d770491b6178` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` | `b605839f-d645-4427-892a-04dd871b7c49` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` | `d042dc77-fd25-4c92-b943-d456ffd86fe9` |
| `Representation.CuspidalSupport.MinimalJacquetProof` | `f28607f5-1eef-4329-ae18-2576ef25ab6a` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` | `5becc159-1242-4fa4-9102-79aa6e2726c0` |
| `Representation.Filtration.SubsingletonProof` | `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` |
| `Representation.Geometric.BlockSixDecomposableProof` | `91670dc7-3166-4d54-b9cb-bcb148f080b5` |
| `Representation.Geometric.BruhatMatrixExistenceProof` | `f22fde8e-f597-44d0-a53d-290de4c59b2d` |
| `Representation.Geometric.BruhatWeylReflectionProof` | `4ff454dd-caa9-435d-8c9b-bc4ed0d4b415` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` | `e71f23b6-a9d9-4bc4-9af9-cde7a187ff8b` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` | `9c98daee-a78a-429a-81dc-4cebbe02dee1` |
| `Representation.Geometric.GeometricLemmaProof` | `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | `1a585c66-e21e-4071-84a0-09a32af9d745` |
| `Representation.Geometric.MonotoneBlocksProof` | `a5db9be0-3f71-4528-89a8-cd92a0c5e411` |
| `Representation.Geometric.OrbitSectionExtensionProof` | `58ca13a3-4bf3-4aaa-8b7d-e8156d189c64` |
| `Representation.Geometric.PadicCorrectionCancellationProof` | `7e7f9c7b-a0fb-4b6a-9539-2d6b9988a4cc` |
| `Representation.Geometric.PadicParabolicBruhatProof` | `b2c9fb09-d2c7-4895-8320-b447e3cc98c6` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` | `18915f54-27ba-4ed6-a6ba-44d2590fd858` |
| `Representation.Geometric.ParabolicSupportGradedProof` | `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.ParabolicSupportJacquetProof` | `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.StandardIntersectionsProof` | `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` | `6e35399b-9029-438e-9663-5ce96ab02576` |
| `Representation.Geometric.WeylUniquenessProof` | `9ad51693-f8a1-45de-949a-72d07ecc13b9` |
| `Representation.Induction.CharacterTwistProof` | `fb3e71c3-36c9-4f69-bc65-3572eba2c084` |
| `Representation.Induction.CompactAutomorphismIntegralProof` | `322d05be-f0c4-46f3-a5ce-0bb0a724e68f` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` | `cbaf9d61-f090-41e3-8269-9ae5a6992693` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` | `9f55d4f4-ce37-42fa-881d-413bffce13e2` |
| `Representation.Induction.CompactLocalSectionSpanningProof` | `0dbbc4e6-1b6c-4682-9e94-bf4b9aa04614` |
| `Representation.Induction.CompactQuotientProof` | `672038be-3175-4fbd-85a6-d8c272aa63ec` |
| `Representation.Induction.CompactSurjectivityProof` | `a757e2b6-b764-46f5-8f53-57f3d2d80f9b` |
| `Representation.Induction.CompactTransitivityProof` | `84a052cc-bc16-4936-b3c5-0e50f92ff0a8` |
| `Representation.Induction.NormalCoinvariantKernelProof` | `89c9c2dc-a112-4cae-b148-3e6de8be0583` |
| `Representation.Induction.NormalCoinvariantProof` | `ffe24f57-d375-48bf-b0ef-536f8cea58dd` |
| `Representation.Induction.SplitQuotientProof` | `75bc696d-7093-45b4-b951-e84ca3cd5f79` |
| `Representation.Induction.SurjectivityProof` | `63c695c6-3dbd-46f6-b675-f46f1aa2a0bb` |
| `Representation.Jacquet.ExactProof` | `d30fdbfc-1ea3-4554-9b0f-540abe813aea` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` | `4c32a273-8e38-4a7c-abb9-f1ad5075ecb9` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` | `9d580fe5-0589-4dfa-9506-1010e413a529` |
| `Representation.Parabolic.QuotientCompactProof` | `400d2277-4574-4aea-a50c-da70cb1702f2` |
| `Representation.Parabolic.UnipotentFiniteContainment` | `cba1f5ba-df9a-4ee7-a403-baaeebbf4d63` |
| `Representation.RankinSelberg.UnipotentUnimodularity` | `4ad92be9-9115-4e7d-b42a-b2adc7dde3e5` |
| `Representation.Smooth.Schur.Proof` | `7418b301-258f-4839-83ff-8b508b8a9abd` |
| `Representation.Smooth.SmallRealizationProof` | `baca19e0-4b51-4368-9b1a-817f6d583c5f` |
| `Representation.Twist.AdmissibilityProof` | `481101cd-15e1-460d-84f8-3bc4331be8b6` |
| `Representation.Twist.SubquotientProof` | `84b8a0ef-a7b9-4ed9-ab40-1b430d7e0f86` |
| `Topology.GroupAction.FiniteOrbitProof` | `72152240-c606-4fc3-87a0-e6d5972c32fa` |
| `Weil.Representation.ContinuityProof` | `8d52aad7-9f5b-41c1-bf76-c1e6483b9639` |
| `Weil.Representation.IsomorphismInvarianceProof` | `53bd2d23-f25a-4747-9ac9-f82617e20070` |
