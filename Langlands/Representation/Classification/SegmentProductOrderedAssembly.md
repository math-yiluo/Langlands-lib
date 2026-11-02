# Ordered segment-product assembly

Author: Worker 593.

This internal module constructs ordered segment-product data and actual smooth
representation isomorphisms for rank transport, a first block with its tail,
and removal of a rank-zero line. It supplies elementary assembly operations
for the highest-derivative proof; it does not assert that derivative formula.
All declarations lie in `Langlands.Classification.SegmentProductOrderedAssembly`.

## Parameters and normalization

Fix `{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}` and the supplied
`T : F.TopologicalData`, installing precisely `T.topology`. The field universe
`uF` and segment universe `uV` are independent. A
`SegmentProductDatum.{uV,uF} T n` has its actual block carriers in
`Type (max uF uV)`. The binary products below are the unchanged normalized
induction functor `T.binaryNormalizedProductFunctor`; the carrier-lift
identifications are explicit representation equivalences. No derivative
functor, additive character, or modulus comparison is assumed here.

## Rank transports and rank-zero factors

`rankCastEquiv` identifies equality transport of a smooth object with its
representation pulled back along the inverse matrix-rank reindexing.
`rankCastSymmEquiv` gives the opposite orientation using forward reindexing.
Both proofs eliminate the equality and use the identity reindexing law.

`nonempty_iso_unit` proves that every supplied smooth representation of
`GL_0(F)` of finrank one is isomorphic to `T.binaryProductUnit`. Mathlib's
one-dimensional linear equivalence identifies the carrier with `ℂ`, and the
inverse `ULift.moduleEquiv` gives the actual unit carrier. The `GL_0` action
is trivial, so this equivalence intertwines both actions. No choice of a
canonical basis or canonical isomorphism is asserted.

`leftUnitIso` and `rightUnitIso` remove the actual binary unit from a product
on either side. They compose the published binary unit equivalence, the
inverse binary tensor carrier-lift equivalence, and the appropriate rank
transport. The remaining object is transported from rank `b` to `0 + b`,
or from rank `a` to `a + 0`, respectively. The factors in these declarations
have the saturated carrier universe `max uF uV`.
`nonempty_iso_omit_left_line` first replaces a supplied rank-zero line by
that unit using the actual binary functor's `mapIso`, then applies
`leftUnitIso`. It requires exactly the displayed finrank-one hypothesis.

## Ordered datum operations

`rankCast h d` changes only the ambient rank equality of a datum. Its
segments and blocks are unchanged. `rankCast_segments`,
`rankCast_hasSegmentSocles`, and `rankCast_induced` record the exact segment
function, preservation of `HasSegmentSocles`, and equality of the induced
object with the functorial rank transport. The last proof again eliminates
the rank equality.

`empty` is the length-zero datum of rank zero. `empty_segments` gives its
exact empty ordered list; `empty_hasSegmentSocles` eliminates an empty index.
`zeroDatumUnitIso` applies the published `emptyProductUnitIso` to every
rank-zero datum, not just the chosen `empty`. Positive block sizes imply
that every such datum has empty block index. `finrank_zeroDatum` transports
finrank through this actual isomorphism to the unit, whose finrank is one.

`cons Δ A d` prepends the supplied segment `Δ` and its actual block `A` to
`d`. Its ambient rank is `Δ.degree + n`; its segments use `Fin.cons` and its
blocks use `Fin.cases`. The sum equality follows from `Fin.sum_univ_succ`.
`cons_segments` is the exact list equality
`List.ofFn (cons Δ A d).segments = Δ :: List.ofFn d.segments`.
`cons_hasSegmentSocles` uses the supplied head and tail socle proofs index
by index. Repeated or equal segments are preserved, and no ordering or
linkage hypothesis is imposed.

`singletonIso d h i`, for `h : d.length = 1`, identifies the induced object
with its supplied block at `i`, transported along
`d.shape.singleBlock_size h i`. It composes actual single-block induction
evaluation with `rankCastEquiv`.

`nonempty_cons_iso_binary` gives an actual category isomorphism between
`(cons Δ A d).induced` and the binary product of `A` with `d.induced`.
For a nonempty tail it applies the published `SegmentProductSplit` head/tail
isomorphism, after eliminating the degree-sum equality. For an empty tail,
the left side is the single block and the right side is its product with
the actual empty unit; compose `singletonIso`, `zeroDatumUnitIso`, and
`rightUnitIso`. This covers the boundary where the usual positive head/tail
shape is unavailable.

`segments_eq_head_cons_tail` states that a datum with at least two entries
has exactly its original first segment followed by the ordered tail from
`SegmentProductSplit.tail`. It is `List.ofFn_succ` after eliminating the
length equality. `rank_sum_eq_head_add_tail` similarly splits the sum of
segment base ranks by `Fin.sum_univ_succ`. Neither lemma permutes indices
or removes duplicates.

## Provenance and dependency audit

The provenance is internal: equality transport, ordinary one-dimensional
linear algebra, actual normalized induction evaluation, tensor units, and
the published head/tail induction-in-stages comparison. There is no new
literature assertion and no classification premise. In particular this
module does not prove a representation irreducible or use a special-head
criterion.

The direct project imports are `Classification.SegmentProductSplit` and
`Induction.EmptyProductUnit`. The external direct import is
`Mathlib.LinearAlgebra.Dimension.Free`. The former project input was
independently accepted as artifact `5440c02b-fc2d-4abe-bbe8-6cd061c6a683` and
published at commit `5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`.
`EmptyProductUnit` was independently accepted as artifact
`273c225f-7fb3-4cf4-852c-88d7816b0bae`, by Reviewer 8857, and published in
integration `351b5bc54d374bde88313e8e0d414501`, commit
`e530d1eb7e66b0d2b988684aaaa90a729bda10e2`. It was authored by Worker 357
under task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, but contains only the
actual empty normalized-product evaluation and unit comparison. It does not
state, import, or prove that task's special-head irreducibility conclusion.
The trusted operator clarification `2b34e4035a5b5dafad7ad84d5a8c0dd8`
distinguishes general infrastructure from excluded mathematical conclusions;
the later clarification `10df3136f50c5901b1061d52c6b92e07` preserves that
distinction. This use is of the independently proved elementary construction.

The recursive project closure was audited at Library commit
`df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e`: 180 project modules including
this new pair, and 102 direct external import roots. All 179 inherited
Lean/Markdown pairs were present, nonempty, and byte-identical to that
Library. After removing comments and strings, a scan found no proof holes,
new axioms, excluded names, or excluded task IDs. The exact project inventory
is recorded below. The inventory is an import inventory, not a claim that
every declaration in every module is used.

Beyond the scan, the implemented proof route uses only the actual rank,
block, tensor, normalized induction and category constructors described
above. `SegmentProductSplit` obtains the comparison by actual induction in
stages, and `EmptyProductUnit` uses full-subgroup evaluation and empty tensor
algebra. The classification portion of this closure contains segment,
supercuspidal, tempered and constituent definitions and lower generic
lemmas, not any excluded classification conclusion. No derivative or
filtration computation is used by this unit.

The audit preserves direct and transitive independence from the complete
exclusions of the host task: unlinked irreducibility; linked reverse-product
structure, reducibility, gluing and quotient maps; juxtaposed reverse-product
structure; socle product irreducibility; adjacent unlinked swaps and
two-segment commutation; ordered multisegment existence and socle exhaustion;
analytic classification; special-head exhaustion and existence; quotient
coverage and ordered conversion; tempered block uniqueness; generic segment
product uniqueness; square-integrable classification and exhaustion;
regular exhaustion; forward special-segment essential square-integrability;
and `SegmentHeadProductIrreducibility`. Their proof successors and any
transitive use of their mathematical conclusions are excluded as well.

The exact forbidden names checked were:

- `AdjacentUnlinkedSegmentSocleSwap`
- `GenericSegmentProductUniqueness`
- `JuxtaposedSegmentSocleReverseProductStructure`
- `LinkedSegmentSocleGluing`
- `LinkedSegmentSoclePairReducible`
- `LinkedSegmentSocleReverseProductQuotientHom`
- `LinkedSegmentSocleReverseProductStructure`
- `OrderedMultisegmentSocleExistence`
- `SegmentHeadProductIrreducibility`
- `SegmentSocleProductIrreducibility`
- `SquareIntegrableLanglandsClassification`
- `TwoSegmentSocleCommutation`
- `UnlinkedSegmentSocleProductIrreducible`

The exact forbidden ownership/task identifiers checked were:

- `1cb45da2-7007-4351-a694-594fb148b8d1`
- `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`
- `23189526-80b0-4828-a6d4-7ebec2cbeef5`
- `23e98d90-6055-4e35-91a9-b0f5d8a84961`
- `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`
- `30341ae4-65f2-4a0e-9283-763db01a409e`
- `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`
- `426911b4-6620-413f-8065-04b25287f3bd`
- `52e97845-36bb-457d-b76f-70753334b88c`
- `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`
- `66e3b87c-647e-41e4-af18-df4d436765f0`
- `6780b79c-9526-46aa-b8b4-00377d68b1ea`
- `7ff2a1e9-89dc-439e-a861-a567b3db92bf`
- `8252833d-c269-41a9-824c-5879e531b23b`
- `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`
- `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`
- `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`
- `aca8805b-054f-4d56-8045-12db7f623404`
- `bf433f0a-921a-428c-b0c0-6475438125ac`
- `c84cd52c-3ff3-4024-be50-8b84dd480888`
- `cd8ab97c-0b78-4bce-97c4-d307a28159a4`
- `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`
- `e3634665-571b-4852-9f4c-bab8a1053434`
- `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`
- `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`

The generic empty-product module's ownership was separately assessed above;
its task ID is not a Lean input and its excluded conclusion is not used.
The final highest-derivative theorem, the actual finite-filtration collapse,
and the single-segment derivative proof remain separate inputs and
obligations; this focused assembly unit supplies none of those assertions.

## Recursive project inventory

```text
Langlands.Group.GL.AdjacentMergeShape
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockUnipotent
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.HeadTailBlocks
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OneBlockShape
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.RefinementCoordinates
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperUnipotent
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.Basic
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Category.UniverseLift
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.SegmentProductOrderedAssembly
Langlands.Representation.Classification.SegmentProductSplit
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Conductor.Congruence
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockEquivalence
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.ConjugateParabolic
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.EmptyProductUnit
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.FiniteProductTensor
Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement
Langlands.Representation.Induction.HeterogeneousConstruction
Langlands.Representation.Induction.HeterogeneousPairs
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.HeadTailProductInduction
Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
Langlands.Representation.Parabolic.OrderedProductRegroupingProof
Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionTensorMap
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorProof
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Parabolic.RefinementTransitivityStatement
Langlands.Representation.Parabolic.RegroupingFactorEquivalences
Langlands.Representation.Parabolic.ThreeBlockCarrierComparison
Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement
Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
Langlands.Representation.Parabolic.ThreeBlockUniverseReduction
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
