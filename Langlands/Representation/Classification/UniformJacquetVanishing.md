# Jacquet vanishing from block divisibility

This internal adapter proves vanishing of actual normalized Jacquet modules
along any target shape with a block not divisible by a common divisor of the
source block sizes. It specializes the published quasicuspidal Jacquet
vanishing theorem, transfers the result to actual smooth subquotients, and
applies it to segment subrepresentations and socles. It supplies a zero-piece
criterion for the juxtaposed-segment argument, not the shuffle Jacquet formula
or the juxtaposed reverse-product structure.

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
for this adapter. The mathematical inputs are imported by their Lean
names. The following table identifies the results used directly.

| Published input | Use here |
| --- | --- |
| `TotalConjugatingCount.blockMap_surjective`, `TotalConjugatingCount.size_blockMap` | Every flattened target block has the size of a source block. |
| `BlockShape.flattenBlockEquiv`, `BlockShape.flatten_size_flattenBlockEquiv` in `CuspidalSupport.MinimalJacquetProof` | Identify the inner refinement sizes before summation. |
| `SegmentEdge.refinedLevi_map_eq_flatten_leviSubgroup` | Rewrite the actual embedded refined-Levi subgroup. |
| `CuspidalSupport.quasicuspidalJacquetVanishing` | Convert the finite obstruction to actual Jacquet vanishing. |
| `CuspidalSupport.subsingleton_of_isSubquotient` in `JacquetVanishingHelpers` | A subquotient of the zero module has zero carrier. |
| `CuspidalSupport.normalizedJacquetSubquotient` | Transport an actual smooth subquotient through normalized Jacquet descent. |
| `CuspidalSupport.glCuspidalTensor` | Supply quasicuspidality of the actual external tensor product. |
| `GeneralLinear.SupercuspidalRep.twist` and the determinant-power character lemmas in `Classification.SupercuspidalTwist` | Package each actual increasing-segment factor as a supercuspidal object. |
| `SmoothRep.IsSubrepresentation.isSubquotient` in `Classification.SupercuspidalSupport` | Use the given injective segment intertwiner as an actual subquotient. |
| The segment definitions and `IsSegmentSocle.isSegmentSubrepresentation` in `Classification.Segments` | Extract the increasing-induction injection from the given segment predicate. |

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
The exact-proof inputs in that closure are inventoried below; each is a
published Library proof. The remaining modules
supply infrastructure, supporting internal lemmas and proposition definitions.
Mathlib supplies finite-sum divisibility and the ordinary algebraic and finite
type infrastructure.

In particular, the imported unconditional geometric lemma is
`Geometric.padicGeometricLemma` (`Geometric.GeometricLemmaProof`). It is an
actual finite-filtration theorem, rather than the separate countability theorem
of `Group.GL.CountabilityProof` proved alongside it.
Its geometric, Haar-measure, compact-support, exactness and Weyl prerequisites
remain upstream of segment classification. The vanishing proof uses that
filtration and quasicuspidality. The subquotient proof uses actual unipotent
coinvariant exactness. The tensor proof uses Schur's lemma and elementary
external-tensor properties. The finite block map uses permutation-matrix
conjugation. The twist proof uses determinant characters and coinvariants.
These routes give no dependency on the excluded classification results.

The audit preserves the full independence requirements of the juxtaposed
reverse-product structure that this module supports:
no linked reverse-product structure or its quotient-homomorphism form;
no linked-pair reducibility or segment-socle product criterion; no adjacent
unlinked socle swap, two-segment socle commutation, linked socle gluing or their
proofs; no ordered multisegment socle existence, socle exhaustion,
segment analytic classification, special-head multisegment exhaustion,
ordered special-head existence, quotient coverage or tempered-block uniqueness;
no square-integrable Langlands classification, square-integrable exhaustion
or regular exhaustion; and no `SegmentHeadProductIrreducibility` or its
conclusions. No derivative construction or derivative theorem occurs in the
closure. These exclusions apply transitively, not just to the three direct
imports. None of the proved modules below is a proof of one of the excluded
results.

This module proves only the stated finite obstruction and its actual
Jacquet-vanishing consequences. It supplies neither a nonvanishing criterion
for divisible shapes nor the remaining exact inputs to
`JuxtaposedSegmentSocleReverseProductStructure`.

### Imported exact-proof inventory

Module names in the following table omit the common `Langlands.` prefix.

| Imported proved module |
| --- |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` |
| `Analysis.Local.QuotientAutomorphismProof` |
| `Analysis.Local.QuotientAveragingKernel` |
| `Analysis.Local.QuotientMeasureExistence` |
| `Analysis.Local.QuotientPositiveLifting` |
| `Group.GL.BlockModulusHaarProof` |
| `Group.GL.BlockUnipotentHaarProof` |
| `Group.GL.CountabilityProof` |
| `Group.GL.UpperBruhatPivotProof` |
| `Group.GL.UpperBruhatProof` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` |
| `HarmonicAnalysis.TriangularTranslationProof` |
| `Representation.CuspidalSupport.AssociationLawsProof` |
| `Representation.CuspidalSupport.CuspidalTensorProof` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` |
| `Representation.CuspidalSupport.MinimalJacquetProof` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` |
| `Representation.Filtration.SubsingletonProof` |
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
| `Representation.Induction.CharacterTwistProof` |
| `Representation.Induction.CompactAutomorphismIntegralProof` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` |
| `Representation.Induction.CompactLocalSectionSpanningProof` |
| `Representation.Induction.CompactQuotientProof` |
| `Representation.Induction.CompactSurjectivityProof` |
| `Representation.Induction.CompactTransitivityProof` |
| `Representation.Induction.NormalCoinvariantKernelProof` |
| `Representation.Induction.NormalCoinvariantProof` |
| `Representation.Induction.SplitQuotientProof` |
| `Representation.Induction.SurjectivityProof` |
| `Representation.Jacquet.ExactProof` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` |
| `Representation.Parabolic.QuotientCompactProof` |
| `Representation.Parabolic.UnipotentFiniteContainment` |
| `Representation.RankinSelberg.UnipotentUnimodularity` |
| `Representation.Smooth.Schur.Proof` |
| `Representation.Smooth.SmallRealizationProof` |
| `Representation.Twist.AdmissibilityProof` |
| `Representation.Twist.SubquotientProof` |
| `Topology.GroupAction.FiniteOrbitProof` |
| `Weil.Representation.ContinuityProof` |
| `Weil.Representation.IsomorphismInvarianceProof` |
