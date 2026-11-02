# Actual factor supports for derivatives of finite ordered products

Author: Worker 357.

This internal constructor selects an actual irreducible constituent of a
derivative of each original factor of an ordered normalized product. The
selected orders add to the supplied derivative order, and the selected support
multisets add to a supercuspidal support of the supplied irreducible constituent.
Finite length of all factor derivatives and suitable supports for all their
irreducible subquotients are explicit hypotheses.

The namespace is `Langlands.Derivative.ProductDerivativeSupport`. The entry
constructor is `supportData`. The same focused unit contains `FactorSupportData`,
`SupportData`, and `supportDataOfSubquotient`.

## Parameters, universes and scope

Fix arbitrary `p : ℕ` with `Fact p.Prime`, a supplied
`F : PadicField.{uF} p`, its supplied `T : F.TopologicalData`, and a supplied
unitary additive character `ψ` for `T.topology`. There is no additional
nontrivial-character hypothesis.

Let `B : GeneralLinear.BlockShape n`, where `0 < n`, and let `hd : d ≤ n`.
The factor family `σ i` consists of actual smooth complex representations of
`GL_(B.size i)(F)`. The supplied `D` is an actual smooth complex representation
of `GL_(n-d)(F)`. Its hypotheses are irreducibility and the constituent-first
relation

```text
SmoothRep.IsSubquotient D
  ((generalLinearDerivative T ψ n d hd).obj
    ((T.normalizedProductInductionFunctor B).obj σ)).
```

All representation carriers in this unit have universe `max uF uV`, with
independent `uF,uV`. Derivatives and equality transport preserve that carrier
universe. Products have the same universe since
`max uF (max uF uV) = max uF uV`.

Support multisets have elements `T.CuspidalDatum.{uV,uF}` at the original
base universe `uV`. The hypotheses supply representatives and actual support
witnesses at this universe. The construction makes no inference that an
arbitrary representation at the larger carrier universe has such a support,
and uses no resizing of cuspidal data.

The block shape has strictly positive block sizes. Positive total rank rules
out the empty shape; singleton shapes are included. Orders `d = 0`, `d = n`,
and selected orders equal to a factor's rank are included. Extracted factors
may therefore have rank zero. The all-rank binary constructions retain their
actual `GL_0` carriers. Repeated factors, repeated segments in a later
application, and all repeated support entries are permitted.

## Selected factor data and explicit hypotheses

For a supplied representation `A` of rank `a` and a supplied predicate

```text
P : ℕ → Multiset (T.CuspidalDatum.{uV,uF}) → Prop,
```

`FactorSupportData T ψ A P` stores:

- `order : ℕ` and `order_le : order ≤ a`;
- an actual smooth representation `factor` of rank `a - order`;
- its irreducibility and actual subquotient occurrence in the `order`-th
  derivative of the original `A`;
- a multiset `cuspidalSupport` at the original datum universe, a proof that it
  is a supercuspidal support of `factor`, and `P order cuspidalSupport`.

For predicates `P i` at the original labels `i : Fin B.length`,
`SupportData T ψ B σ D P` stores a `FactorSupportData` for every original
`σ i`, together with

```text
∑ i, (factors i).order = d,
T.IsSupercuspidalSupport D (∑ i, (factors i).cuspidalSupport).
```

The sums are finite sums over the original labels. Support addition is
multiset addition, preserving every multiplicity. The final structure retains
each actual factor and its occurrence in its original factor derivative.
The intermediate binary subspace/kernel/isomorphism presentations are used
in the construction but are not fields of this final structure.
Neither structure itself includes the original occurrence premise for `D`;
the constructors take that premise explicitly.

`supportData` assumes:

```text
hFinite :
  ∀ i k (hk : k ≤ B.size i),
    ((generalLinearDerivative T ψ (B.size i) k hk).obj (σ i)).HasFiniteLength
```

and, uniformly for every such `i,k,hk` and every actual irreducible subquotient
`E` of that derivative,

```text
hSupport :
  ∃ s, P i k s ∧ T.IsSupercuspidalSupport E s.
```

It also takes `0 < n`, `hd`, irreducibility of `D` and its actual derivative
occurrence. These hypotheses are not conclusions of this unit.

## Implemented construction

The private `supportData_nonempty` proves existence by strong induction on
the number of blocks. The entry `supportData` uses `Classical.choice`
on that established nonempty type. No canonical choice or uniqueness is
asserted.

Rank comparisons are handled by equality elimination. The helpers
`rankCast_irreducible`, `rankCast_support_back`, and
`derivative_rankCast_occurrence` eliminate their supplied rank equality;
the last pulls a constituent back from a derivative of a rank-transported
object. The helper `rankCast_binary_support` similarly eliminates its rank
equality before applying the proved general
`T.binaryProductConstituentSupport`. These steps identify actual objects
and occurrences and assume no derivative formula.

### Empty and singleton cases

An empty `Fin B.length` makes the block-size sum zero. The equality
`B.sum_eq` then contradicts `0 < n`.

For a singleton, `i = B.singleBlockIndex h` is its unique original label.
The published `singleBlock_size` gives `e : B.size i = n`.
The private `singletonProductIso` identifies the actual normalized product
with `generalLinearRankCast T e` applied to `σ i`. It composes
`normalizedProductInductionObjEquiv`, the actual
`singleBlockTransportedProductEquiv`, and equality transport. The family
comparison uses cancellation of transport followed by inverse transport;
`rankCast_obj_transport` compares the bundled rank-cast object's value
with that equality transport.

Map this singleton isomorphism through the derivative and transport the
supplied `D` back along the residual-rank equality. This gives an actual
irreducible `D₀` in the `d`-th derivative of `σ i`. Apply the supplied
`hSupport` at exactly this object and order and select its supplied
support. This provides the sole `FactorSupportData`.
`sum_singleBlock` proves both finite-sum identities. Equality elimination
transports the support of `D₀` back to a support of `D`.
The singleton case needs no application of `hFinite`.

### First factor and ordered tail

Suppose `B.length = m + 2`. Let `A` be the original first factor
`σ (B.headIndex h)` and let `C` be the actual normalized product of the
family `σ (B.tailIndex h j)` on `B.tailShape h`, in its original order.
Both source ranks are positive. Write

```text
e : B.headRank h + B.tailRank h = n.
```

Map `T.headTailBinaryProductIso B h σ` through the supplied derivative.
Its target is equality transport of the literal all-rank binary product
of this original `A` and this actual `C`. Pull `D` back along
`congrArg (fun r => r - d) e` to obtain `D₀` and its actual occurrence
in that binary-product derivative.

The published
`ProductDerivativesFiniteLength.product_derivatives` supplies finite length
of every derivative of `C`, using the original `hFinite` restricted to the
tail labels. The original head's derivative finite length is supplied
directly by `hFinite`.

Apply `BinaryDerivativeSupport.factorData` to `A,C,D₀`. It produces a
feasible index `(i,j)` with `i+j=d`, actual irreducible constituents
`f.left` of `A^(i)` and `f.right` of `C^(j)`, their actual occurrences,
and an invariant subspace, kernel and smooth quotient isomorphism
presenting `D₀` in the prescribed rank cast of `f.left × f.right`.

Apply `hSupport` at the original head, order `i` and actual `f.left`.
This selects its supplied support and head `FactorSupportData`.
Apply the induction hypothesis to the actual ordered tail at order `j`
and actual constituent `f.right`. Tail source rank is positive, even
when its residual rank is zero. Every tail premise is the original
premise restricted by `B.tailIndex h`. This returns data indexed by the
tail factors and a support of `f.right` equal to their sum.

The private `headTailPi` assembles this dependent head and tail data over
the original labels of `B`; its proof destructs the shape and uses
`Fin.cases`. Its head and tail computation lemmas preserve those labels.
`sum_headTail` decomposes sums at exactly the same indices.
The tail's `order_sum` and `leibnizIndices_sum` prove the final order sum.

For the support sum, `rankCast_binary_support` combines the chosen head
support with the tail's summed support. Its occurrence premise is the
actual `f.subspace`, `f.kernel` and `f.occurrenceIso`.
Rewrite with `sum_headTail` and transport back from `D₀` to `D`.
This proves the required support of `D`.

### A supplied source subquotient

`supportDataOfSubquotient` permits an additional supplied `Q` of rank `n`
with an actual occurrence in the original normalized product. Its premise
on `D` is an occurrence in the `d`-th derivative of this `Q`.
It takes the same `hFinite`, `hSupport` and irreducibility premise for `D`.
There is no irreducibility or finite-length premise on `Q`.

The published `generalLinearDerivativeExactness` and
`ExactSmoothTransport.map_isSubquotient` map the actual occurrence of `Q`
through the derivative. The published `smoothSubquotientTransitivity`
composes it with the supplied occurrence of `D`. The result is exactly
the premise needed by `supportData`, which supplies the returned data.

## Internal provenance and direct inputs

The provenance is internal and the source list is empty. This pair
translates no new external theorem. Its three direct imports have the
following roles.

| Module after `Langlands.Representation.` | Role |
| --- | --- |
| `Derivative.BinaryDerivativeSupportAggregation` | Feasible actual simple derivative-factor constituents and their product occurrence, general support addition, derivative exactness and actual subquotient transitivity |
| `Induction.HeadTailBinaryProduct` | Actual isomorphism to the rank-cast literal binary product on the original head and ordered tail |
| `Derivative.ProductDerivativesFiniteLength` | Finite length of every derivative of the actual tail product, conditional on the supplied derivative finite length of its original factors |

The inherited binary extraction follows the actual general Leibniz
filtration, finite-filtration constituent extraction and composition-series
product filtrations. The support-addition theorem concatenates supplied
cuspidal families, constructs their actual product occurrence in the
concatenated induction and composes actual subquotient presentations.
It assumes no support uniqueness.

The first/tail comparison follows the proved closed ordered-regrouping
theorem, actual tensor/induction comparisons, the inverse carrier-lift
equivalence on the head and equality transport. It preserves the original
head object and actual ordered tail.

The tail finite-length theorem uses general binary Leibniz filtrations,
finite length of the binary products of finite-length factors, and
induction on the ordered block shape. The positive-rank binary step uses
proved general normalized-product finite length and finite-length
admissibility. Zero-rank binary factors use actual tensor models and
finite-dimensionality for the trivial group. Its imported module also
proves the independently permitted supercuspidal derivative finite-length
case, but the call here is the general conditional `product_derivatives`,
with every factor premise supplied explicitly.

## Dependency audit

At the refreshed Library base
`578442903325ac58fd3108d9bb76624bb791faf9`, the recursive inventory has
961 project modules including this entry, and 294 directly named external
import roots. Every inherited module has a nonempty paired Markdown file.
There are no missing project imports. The complete inventory below
recurses through project imports and lists external roots directly; it
does not claim a separate recursive traversal of Mathlib.

All 960 inherited Lean/Markdown pairs are byte-identical to that Library.
The first/tail adapter is now independently accepted and published, and
its pair at this base is identical to the frozen reviewed pair. The
refreshed inventory has the same project and external names and inherited
fingerprints as the earlier recovery audit. No new inherited source
change remains to reconcile.

The audit compared fingerprints with the earlier binary aggregation,
first/tail adapter, head-product finite-length, dual-head and top-head
inventories. Outside their union are this entry, the fully read
`ProductDerivativesFiniteLength` pair and the following sixteen pairs,
each read in full with its Markdown:

- `Group.GL.NestedRefinement`;
- `Representation.Classification.NormalizedProductFiniteLengthProof`;
- `Representation.CuspidalSupport.IrreducibleLeviAdmissibilityStatement`
  and `IrreducibleLeviAdmissibilityProof`;
- `Representation.CuspidalSupport.MinimalRefinedJacquetStatement`
  and `MinimalRefinedJacquetProof`;
- `Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingStatement`
  and `RefinedQuasicuspidalEmbeddingProof`;
- `Representation.Filtration.FactorMatchingPullback`
  and `JordanHolderProof`;
- `Representation.Parabolic.ExactnessReciprocityStatement`
  and `InductionExactnessProof`;
- `Representation.Smooth.Admissibility.FiniteLengthStatement`
  and `FiniteLengthProof`;
- `Representation.Tensor.FactorMatchingStatement`
  and `FactorMatchingProof`.

All names in this list have prefix `Langlands.`. The only historical
fingerprint mismatch among the earlier covered pairs is completion of the
binary aggregation's documentation after its earlier inventory. Its
accepted published pair was read and matched. Recovery against the
current base leaves no new inherited fingerprint change.

The newly inspected routes are general infrastructure. Nested refinement
preserves actual ordered coordinates, using the composite numbering and
identity of a strictly monotone finite self-map.
Minimal refined Jacquet chooses maximal flattened block count and
constructs a surjection from the composed Jacquet quotient to the iterated
coinvariants. The radical's actual inverse half-modulus is one where
needed. This is a general quotient comparison.

Refined quasicuspidal embedding constructs finite orbit classes from a
compact refined-parabolic double-coset cover, chooses a maximal
subrepresentation quotient and uses actual refined Frobenius reciprocity.
Irreducibility makes its map injective. Irreducible Levi admissibility
combines that embedding, general quasicuspidal admissibility, coordinate
transport and refined induction admissibility. Finite-length admissibility
then follows by a composition-length induction and exact admissibility
extensions.

Tensor factor matching uses actual tensor filtrations, graded refinement,
admissible Schur arguments and external tensor irreducibility, then finite
head/tail recursion. General normalized-product finite length combines
irreducible Levi factorization, published irreducible-product finite
length, exact normalized induction and composition series.
Normalized-induction exactness uses actual pointwise image/kernel
calculations and published smooth-induction surjectivity; its normalization
is an invertible half-character twist. These proofs introduce no segment
conclusion, classification input or circular irreducibility premise.

Exactly 27 `Classification` modules occur in this closure:
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`,
`FiniteLengthStatement`, `IrreducibleProductEmbedding`,
`IrreducibleProductEmbeddingStatement`, `IrreducibleProductFiniteLengthProof`,
`NormalizedProductFiniteLengthProof`, `NormalizedProductFiniteLengthStatement`,
`RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`,
`RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
`SupercuspidalDerivativeVanishing`, `SupercuspidalDerivativesProof`,
`SupercuspidalDerivativesStatement`, `SupercuspidalSupport`,
`SupercuspidalTopDerivative`, `SupercuspidalTwist`, `Tempered`,
`TemperedInductionStatement` and `TemperedSupportStatement`.
The actual general proofs just described supply the inputs used here.
Broader Prop-valued statement interfaces inherited through imports are not
treated as established conclusions.

## Host independence boundaries

The trusted operator responses
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md),
and [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
were read in full. They permit independently proved general derivative
infrastructure while retaining all host exclusions. The third separately
permits a newly proved exactly support-only terminal-truncation bound.
This constructor proves no such segment bound and uses none as an input.

| Excluded result or boundary | Check on the closure and implemented route |
| --- | --- |
| Ze80 §§3.5/9.6, their formulas, proofs and proof successors | No segment derivative formula is imported or invoked. The derivative routes are general Leibniz, exactness and permitted supercuspidal derivative theory. |
| Full segment/head/socle Jacquet formulas and exponent norm formula, including tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | None supplies a proof dependency. General refined Jacquet quotient and embedding arguments apply no such formula. |
| Host criterion `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` in either direction and socle product criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Neither conclusion, a proof successor nor a downstream criterion consumer is imported or used. |
| Parent uniqueness `30341ae4-65f2-4a0e-9283-763db01a409e` | No uniqueness or comparison of different segment products is used. |
| Multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | None supplies an input. The original factor family is supplied and the recursion preserves its ordered labels. |
| Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`, `SquareIntegrableLanglandsClassification` and task `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | These conclusions and their proof routes are absent. |
| Segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` | Absent. The separate independently proved supercuspidal-derivative part is present and permitted; the segment-socle derivative statement and its successors are absent. |
| Linked-pair structure, adjacent commutation and two-supercuspidal product criteria | None supplies an input. General normalized-product finite length and actual product filtrations require no such criterion. |
| Whittaker irreducible/Levi/supercuspidal coinvariant finiteness and dependent mirabolic finite length | These excluded routes are absent. The tail argument uses independently proved general product finite length and explicit finite-length hypotheses on original factor derivatives. |
| Original datum universe and repeated support entries | Actual carriers remain at `max uF uV`, supplied support witnesses remain at original `uV`, and multiset sums retain all multiplicities. |
| Segment results and run controls | No support-only segment proof or stronger intermediate from it supplies an input. Every inherited pair, including the general adapter, is published at the recorded Library base. No paused owner is contacted or needed to finish this construction. |

A recursive lexical scan after removing nested comments and strings found
no audited excluded-name or task-identifier matches, proof holes, new
axioms or prohibited execution syntax. The actual route inspection above
supplements that scan; a name scan alone would not establish independence.

## Development validation and remaining scope

Approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
complete private module, including `supportDataOfSubquotient`, with zero
errors and warnings in check `c3b686ed-52a3-4b4e-8f6f-a7d10ca3b49e`.
Recovery check `f611303d-7ceb-4fe4-b65d-5090483514b7` reproduced that result
and inspected the exact entry `supportData`: kind `definition`, independent
levels `uF,uV`, and only `propext`, `Classical.choice` and `Quot.sound`.
Refreshed-base recovery checks
`6412648e-bc5c-4ef2-bf82-3d7c493dcc02` (ordinary binary aggregation and
first/tail adapter) and `ed497a8f-5d13-42e8-a340-6e4bc3d28bf6` (complete
private entry and exact declaration) again returned zero errors and
warnings, with the same entry kind, universe parameters and allowed
axioms. The final ordinary-module check
`585daab3-94d0-491c-af6f-4cfd4f47fb8c` compiled this same complete Lean
source and inspected the exact entry with zero errors and warnings,
confirming the same declaration kind, universe parameters and axioms.
No Lean edit followed these checks. Development checks establish neither
independent semantic acceptance nor publication.

This unit proves finite-product support aggregation from its explicit
hypotheses. It proves no unconditional factor-support existence, support
uniqueness, equality with an independently specified support, derivative
irreducibility, truncated-head identification, multiplicity statement or
full segment derivative formula. A future application to special heads
still needs permitted factor finite length and segment support bounds.
The dual initial bound, support comparison needed by the host,
nonlinkage survival and the linked converse remain separate obligations.
The full repeated-segment special-head product irreducibility criterion
remains unproved by this contribution.

## Complete import inventory

Each prefix below is followed by its immediate module suffixes; concatenating
them with a dot expands to the full import names. Project imports are recursive.
External names are directly named roots from those project modules.

### Project modules

- `Langlands.Algebra`: `CommutingDimensionHelpers`, `CommutingDimensionNilpotent`, `CommutingDimensionNumerics`, `CommutingDimensionPrimary`, `CommutingDimensionRecurrence`, `MultisetOfFn`, `SandwichDimensionBoundProof`, `SandwichDimensionBoundStatement`, `SeparatedMatrixRepresentations`.
- `Langlands.Analysis.Local`: `CompactOpenCoverUnimodularityProof`, `CompactOpenCoverUnimodularityStatement`, `ModularCompactAverage`, `QuotientAutomorphismProof`, `QuotientAutomorphismStatement`, `QuotientAverageReal`, `QuotientAveragingKernel`, `QuotientComplex`, `QuotientFunctional`, `QuotientMass`, `QuotientMeasure`, `QuotientMeasureExistence`, `QuotientMeasureExistenceStatement`, `QuotientMeasurePrerequisites`, `QuotientPositiveLifting`, `QuotientTopology`, `QuotientTranslation`, `SplitKernelQuotient`.
- `Langlands.ClassFieldTheory.Local`: `Completion`, `FiniteArtin`, `Galois`, `Norms`, `ProfiniteReciprocityStatement`, `ReciprocityRelations`, `Transfer`, `Units`, `WeilAbelianization`, `WeilReciprocityStatement`.
- `Langlands.Combinatorics`: `RelationInversions`.
- `Langlands.Correspondence`: `AutomorphicRelations`, `Domains`, `LocalConventions`, `OperationCompatibility`, `SupercuspidalRelations`, `UnramifiedNormalization`.
- `Langlands.Galois.FiniteField`: `Comparison`, `ComparisonProof`, `Frobenius`.
- `Langlands.Galois.Local`: `AbsoluteDefinitions`, `AbsoluteProof`, `AbsoluteStatement`, `SpectralDefinitions`, `SpectralProof`, `SpectralStatement`.
- `Langlands.Group`: `HaarModulus`, `LeftQuotient`.
- `Langlands.Group.GL`: `AdjacentMergeShape`, `Basic`, `BlockContractionProof`, `BlockContractionStatement`, `BlockDeterminant`, `BlockIwahoriBasis`, `BlockIwahoriBasisStatement`, `BlockIwahoriDefinitions`, `BlockModulus`, `BlockModulusHaarProof`, `BlockModulusHaarStatement`, `BlockUnipotent`, `BlockUnipotentCoordinates`, `BlockUnipotentHaarProof`, `BlockUnipotentHaarStatement`, `Blocks`, `CartanProof`, `CartanStatement`, `CompactOpen`, `CountabilityProof`, `CountabilityStatement`, `DominantExponentGeneration`, `HeadTailBlocks`, `IntegralSubgroup`, `Maps`, `Mirabolic`, `MirabolicMixedOrbitCoverageProof`, `MirabolicMixedOrbitCoverageStatement`, `MirabolicMixedOrbitData`, `MirabolicMixedOrbitRadicals`, `MirabolicMixedOrbitSectionCoefficients`, `MirabolicMixedOrbitSections`, `MirabolicMixedOrbitSpecializations`, `MirabolicMixedOrbitStages`, `MirabolicMixedProductSubgroups`, `MirabolicModularCharacterProof`, `MirabolicModularCharacterStatement`, `MirabolicModulusProof`, `MirabolicModulusStatement`, `MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`, `NestedRefinement`, `Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`, `OneBlockShape`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `PadicOppositeBlocks`, `PadicUpperUnipotent`, `PrincipalBlockFactorizationProof`, `PrincipalBlockFactorizationStatement`, `PrincipalLevelDominance`, `RankMaps`, `RankReindex`, `RefinementCoordinates`, `ReindexCongr`, `ReverseBlocks`, `SingleBlock`, `SingletonBlocks`, `Transvection`, `TriangularParabolic`, `UnramifiedCharacter`, `UpperBruhatBoundaryProof`, `UpperBruhatBoundaryStatement`, `UpperBruhatCells`, `UpperBruhatCoordinatesProof`, `UpperBruhatCoordinatesStatement`, `UpperBruhatEmbedding`, `UpperBruhatFiltration`, `UpperBruhatFiltrationGeometryProof`, `UpperBruhatFiltrationGeometryStatement`, `UpperBruhatLocalClosednessProof`, `UpperBruhatLocalClosednessStatement`, `UpperBruhatPivotProof`, `UpperBruhatPivotStatement`, `UpperBruhatProof`, `UpperBruhatRankProof`, `UpperBruhatRankStatement`, `UpperBruhatStatement`, `UpperBruhatTransposeProof`, `UpperBruhatTransposeStatement`, `UpperUnipotent`, `UpperUnipotentCompactContainmentProof`, `UpperUnipotentCompactContainmentStatement`, `UpperUnipotentFactorizationProof`, `UpperUnipotentFactorizationStatement`.
- `Langlands.HarmonicAnalysis`: `AlgebraicIntegral`, `AlgebraicIntegrand`, `Basic`, `CharacterTransport`, `Conductor`, `FiniteProductMeasureScaling`, `HaarConjugacy`, `PadicAdditiveConductorProof`, `PadicHaarScalingStatement`, `PadicLatticeTopology`, `PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`, `RowFourier`, `RowTensorDecompositionProof`, `RowTensorDecompositionStatement`, `TriangularTranslationProof`, `TriangularTranslationStatement`.
- `Langlands.HarmonicAnalysis.Distribution`: `Basic`, `BruhatFiltrationVanishingProof`, `BruhatFiltrationVanishingStatement`, `CharacterAverage`, `CharacterAverageCovarianceProof`, `CharacterAverageCovarianceStatement`, `CharacterAverageFactorizationProof`, `CharacterAverageFactorizationStatement`, `CharacterAverageSurjectiveProof`, `CharacterAverageSurjectiveStatement`, `ClosedRestrictionProof`, `ClosedRestrictionStatement`, `ClosedSupportedDescentProof`, `ClosedSupportedDescentStatement`, `FiniteOrbitVanishingProof`, `FiniteOrbitVanishingStatement`, `GeneralLinear`, `HomogeneousPositivityProof`, `HomogeneousPositivityStatement`, `HomogeneousVanishingProof`, `HomogeneousVanishingStatement`, `LocalizationProof`, `LocalizationStatement`, `OpenRestrictionLocalityProof`, `OpenRestrictionLocalityStatement`, `Subspace`, `SupportedDescentCovarianceProof`, `SupportedDescentCovarianceStatement`, `SupportedRestriction`, `TransposeInvariantProof`, `TransposeInvariantStatement`.
- `Langlands.LinearAlgebra`: `CyclicQuotientPairingProof`, `CyclicQuotientPairingStatement`, `FiniteRankTrace`, `FiniteRankTranspose`, `MatrixAEvalConjugacyProof`, `MatrixAEvalConjugacyStatement`, `MatrixCharpolyConjugacyProof`, `MatrixCharpolyConjugacyStatement`, `MatrixTransposeConjugateProof`, `MatrixTransposeConjugateStatement`, `PolynomialModuleBoundedCyclicDecompositionProof`, `PolynomialModuleBoundedCyclicDecompositionStatement`.
- `Langlands.LocalFactor`: `Euler`, `RankOne`.
- `Langlands.LocalFactor.Euler`: `Definitions`.
- `Langlands.LocalFactor.Harmonic`: `Statement`.
- `Langlands.LocalField`: `Canonical`, `CanonicalProof`, `CanonicalStatement`, `Definitions`, `Topology`, `Uniformizer`.
- `Langlands.LocalField.Normalization`: `Definitions`, `Proof`, `Statement`.
- `Langlands.Representation`: `OrbitSpan`, `SubrepresentationLattice`.
- `Langlands.Representation.Category`: `Abelian`, `Basic`, `ClassInvariants`, `Subquotients`, `Twist`, `UniverseLift`.
- `Langlands.Representation.Character`: `Basic`, `SeparationProof`, `SeparationStatement`, `TransportProof`, `TransportStatement`.
- `Langlands.Representation.Classification`: `CanonicalConstituents`, `ConstituentRelations`, `CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`, `FiniteLengthStatement`, `IrreducibleProductEmbedding`, `IrreducibleProductEmbeddingStatement`, `IrreducibleProductFiniteLengthProof`, `NormalizedProductFiniteLengthProof`, `NormalizedProductFiniteLengthStatement`, `RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`, `RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`, `SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`, `SupercuspidalDerivativeVanishing`, `SupercuspidalDerivativesProof`, `SupercuspidalDerivativesStatement`, `SupercuspidalSupport`, `SupercuspidalTopDerivative`, `SupercuspidalTwist`, `Tempered`, `TemperedInductionStatement`, `TemperedSupportStatement`.
- `Langlands.Representation.Compact`: `Definitions`, `FiniteMean`, `OrbitMeanTranslation`, `ProjectionProof`, `ProjectionStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.CompactCoefficient`: `AdmissibleComplement`, `AdmissibleLifting`, `AdmissibleRetraction`, `AmbientProjector`, `Classes`, `ConditionalProjection`, `FixedLevelFiniteness`, `FixedVectorsFiniteDimensional`, `GroupTransport`, `Isotypic`, `IsotypicTransport`, `NormalSubgroupDecomposition`, `OrthogonalProjectorFamily`, `SemisimplicityProof`, `SemisimplicityStatement`, `TotalCompactness`, `TotalProjector`.
- `Langlands.Representation.Conductor`: `Congruence`, `Definitions`, `PrincipalCongruence`, `PrincipalCongruenceBasisProof`, `PrincipalCongruenceBasisStatement`.
- `Langlands.Representation.CuspidalSupport`: `AllRankBinaryCuspidalConcatenation`, `AssociatedAssembly`, `AssociatedConditional`, `AssociatedGeometricPieceVanishingProof`, `AssociatedGeometricPiecesEquivalenceProof`, `AssociatedGeometricPiecesProof`, `AssociatedGeometricPiecesStatement`, `AssociatedProof`, `AssociatedRankZero`, `AssociationForwardStatement`, `AssociationLawsProof`, `AssociationLawsStatement`, `AssociationReduction`, `BinaryCuspidalConcatenation`, `BinaryProductSupport`, `BlockMap`, `BlockPermutation`, `CompactCoefficientFinitenessProof`, `CompactCoefficientFinitenessReduction`, `CompactCoefficientFinitenessStatement`, `CuspidalEmbeddingProof`, `CuspidalTensorAssociationProof`, `CuspidalTensorProof`, `CuspidalTensorStatement`, `CuspidalityComparisonProof`, `CuspidalityComparisonStatement`, `DeterminantUnit`, `DeterminantUnitCartanSupport`, `DeterminantUnitCentralCompactnessProof`, `DeterminantUnitCentralCompactnessStatement`, `DeterminantUnitCornerStructureProof`, `DeterminantUnitCornerStructureStatement`, `DeterminantUnitStructureProof`, `DeterminantUnitStructureStatement`, `DualAveraging`, `FiltrationQuasicuspidality`, `FiniteBlockShapes`, `GroupTransport`, `HarishChandraAssembly`, `HarishChandraBoundaryProof`, `HarishChandraBoundaryStatement`, `HarishChandraConverseProof`, `HarishChandraConverseStatement`, `HarishChandraForwardProof`, `HarishChandraStatement`, `InducedJacquetCount`, `InducedJacquetEvaluation`, `IrreducibleLeviAdmissibilityProof`, `IrreducibleLeviAdmissibilityStatement`, `JacquetDetectingFamilyLengthProof`, `JacquetDetectingFamilyLengthStatement`, `JacquetInductionStatement`, `JacquetLengthDetector`, `JacquetSubquotientProof`, `JacquetSubquotientStatement`, `JacquetVanishingHelpers`, `JacquetVanishingSmoothPieces`, `JacquetVanishingSubgroups`, `LeviAdmissibleFactorizationProof`, `LeviAdmissibleFactorizationStatement`, `LeviAssociation`, `LeviCompactPart`, `LeviDecompositionAssembly`, `LeviDefinitions`, `LeviGapVanishing`, `LeviQuasicuspidalDecompositionProof`, `LeviSplitContraction`, `LeviTensorFactorizationProof`, `LeviTensorFactorizationStatement`, `LeviTensorReflectionProof`, `LeviTensorReflectionStatement`, `MinimalConjugatingCosetsProof`, `MinimalJacquetProof`, `MinimalJacquetStatement`, `MinimalRefinedJacquetProof`, `MinimalRefinedJacquetStatement`, `MinimalWeylTransportProof`, `NaturalProjectorDecomposition`, `NonassociatedJacquetSubquotientsProof`, `NormalizedCuspidalInductionLengthProof`, `NormalizedCuspidalInductionStatement`, `PointwiseProjectorSum`, `ProperInductionMaps`, `ProperInductionProof`, `ProperInductionStatement`, `QuasicuspidalEmbeddingProof`, `QuasicuspidalFiniteLengthProof`, `QuasicuspidalFiniteLengthStatement`, `QuasicuspidalLeviAdmissibilityProof`, `QuasicuspidalPrerequisitesStatement`, `QuasicuspidalStructureStatement`, `RefinedJacquetLengthProof`, `RefinedJacquetLengthStatement`, `RefinedQuasicuspidalEmbeddingProof`, `RefinedQuasicuspidalEmbeddingStatement`, `StandardJacquetComparisonProof`, `TotalConjugatingCountProof`, `TotalConjugatingCountStatement`, `ZeroRankEmbeddingProof`.
- `Langlands.Representation.Derivative`: `BinaryDerivativeSupportAggregation`, `GeneralLinearDerivativeExactnessProof`, `GeneralLinearDerivativeExactnessStatement`, `GeneralLinearDerivativeLeibnizBoundary`, `GeneralLinearDerivativeLeibnizFiltrationProof`, `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeftMixedProductDerivativeProof`, `LeftMixedProductHigher`, `LeftMixedProductVanishing`, `LeftMixedProductZeroRank`, `LeibnizConstituentExtraction`, `LeibnizIndices`, `LeibnizPieceCompat`, `LeibnizPositiveGluing`, `LeibnizQuotientPiece`, `LeibnizRankZeroBoundary`, `LeibnizRankZeroGluing`, `LeibnizRestrictionCompat`, `LeibnizRestrictionExact`, `LeibnizZeroFirstPiece`, `LevelCalculus`, `MinusVanishing`, `MirabolicCharacter`, `MirabolicDerivativeDetectionProof`, `MirabolicDerivativeDetectionStatement`, `MirabolicDerivativeVanishing`, `MirabolicDeterminant`, `MirabolicLatticeBox`, `MirabolicMinus`, `MirabolicMinusExactnessProof`, `MirabolicMinusExactnessStatement`, `MirabolicMixedOrbitCharacters`, `MirabolicPhiMinusMackey`, `MirabolicPlus`, `MirabolicProductMinusBoundary`, `MirabolicProductMinusCompatibilityStatement`, `MirabolicProductMinusLeftPhi`, `MirabolicProductMinusLeftPhiCoefficient`, `MirabolicProductMinusLeftPhiCompactComparison`, `MirabolicProductMinusLeftPhiHaar`, `MirabolicProductMinusLeftPhiHostTransport`, `MirabolicProductMinusLeftPhiIdentityComparison`, `MirabolicProductMinusLeftPhiInductionNormalization`, `MirabolicProductMinusLeftPhiLocalization`, `MirabolicProductMinusLeftPhiMackeyLocalization`, `MirabolicProductMinusLeftPhiNormalization`, `MirabolicProductMinusLeftPhiNormalizedSection`, `MirabolicProductMinusLeftPhiSection`, `MirabolicProductMinusLeftPhiSourceAction`, `MirabolicProductMinusLeftPhiSourceComparison`, `MirabolicProductMinusLeftPhiStagesComparison`, `MirabolicProductMinusLeftPsi`, `MirabolicProductMinusLeftPsiInduction`, `MirabolicProductMinusPhiKernelComparison`, `MirabolicProductMinusRightBoundary`, `MirabolicProductMinusRightPhi`, `MirabolicProductMinusRightPhiAssembly`, `MirabolicProductMinusRightPhiCycle`, `MirabolicProductMinusRightPhiCycleCoefficient`, `MirabolicProductMinusRightPhiCycleGroups`, `MirabolicProductMinusRightPhiIdentity`, `MirabolicProductMinusRightPhiIdentityCoefficient`, `MirabolicProductMinusRightPhiIdentityGroups`, `MirabolicProductMinusRightPsi`, `MirabolicProductMinusRightPsiCoefficient`, `MirabolicProductMinusRightPsiGroups`, `MirabolicProductMinusRightPsiZero`, `MirabolicProductRestriction`, `MirabolicProductRestrictionCasts`, `MirabolicProductRestrictionFactors`, `MirabolicProductRestrictionMackey`, `MirabolicProductRestrictionOrbits`, `MirabolicProductRestrictionStabilizers`, `MirabolicProductRestrictionStatement`, `MirabolicProductRestrictionTransport`, `MixedProductDerivativeStatement`, `MixedProductRankCast`, `OrderRecursion`, `ProductDerivativeSupportAggregation`, `ProductDerivativesFiniteLength`, `ProductVanishing`, `RankCastCompat`, `RightMixedProductDerivativeFiltrationProof`, `RightMixedProductDerivativeFiltrationStatement`, `RightMixedProductDerivativePositive`, `RightMixedProductZeroRank`, `ShortExactFunctorLaws`, `ZeroRankTensor`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Exponents`: `Central`, `ComplexTwistFamilies`, `DualJacquet`, `DualJacquetStatement`, `Jacquet`, `NilpotenceIndex`, `ParabolicPair`, `RealTwistFamilies`, `SupportedRegularMultiplicityBranchObstructionStatement`, `WeylBranchPiecesStatement`, `WeylBranchPiecesSubquotient`.
- `Langlands.Representation.Filtration`: `ActualGradedExtraction`, `CoarseJacquetExtraction`, `CoarseJacquetFactorization`, `CoinvariantVanishingStatement`, `Definitions`, `ExactConstituentExtraction`, `ExactSmoothSubquotients`, `ExactSmoothTransport`, `FactorMatchingPullback`, `GluedFamily`, `GradedRefinementProof`, `GradedRefinementStatement`, `IntervalLiftProof`, `IntervalLiftStatement`, `IrreducibleEmbedding`, `IsoTransport`, `JordanHolderComparisonProof`, `JordanHolderProof`, `JordanHolderStatement`, `JordanHolderTransportProof`, `LengthCriterionProof`, `LengthCriterionStatement`, `LengthTwoMatching`, `LengthTwoMatchingStatement`, `MultiplicityStatement`, `ObjectDefinitions`, `ObjectTransport`, `OneStep`, `Precomposition`, `QuasicuspidalVanishingProof`, `QuotientFirstIso`, `QuotientTail`, `RepresentationLength`, `SmoothGradedObject`, `Splicing`, `SubquotientAlgebraProof`, `SubquotientAlgebraStatement`, `SubsingletonProof`, `Transport`, `VanishingStatement`, `ZeroFactorDeletionProof`, `ZeroFactorDeletionStatement`.
- `Langlands.Representation.Filtration.Splicing`: `Basic`.
- `Langlands.Representation.Geometric`: `BlockIntersectionSplitting`, `BlockSixDecomposableProof`, `BlockSixDecomposableStatement`, `BruhatDescent`, `BruhatMatrixExistenceProof`, `BruhatMatrixStatement`, `BruhatWeylReflectionProof`, `ClosedSubgroupAssembly`, `ClosedSubgroupDefinitions`, `ClosedSubgroupMackeyProof`, `ClosedSubgroupStatement`, `CompactOrbitRestriction`, `CompactSmoothComparison`, `ConditionalAssembly`, `CorrectionSubgroupCoordinates`, `CorrectionSubgroupDiagonalHaarProof`, `CorrectionSubgroupDiagonalHaarStatement`, `CosetAction`, `CosetOrbitHomeomorph`, `CosetOrbitOrdering`, `FlattenedLevi`, `GeneralCorrectionCharacters`, `GeneralIntersectionNormalizers`, `GeneralIntersections`, `GeometricLemmaProof`, `GeometricLemmaStatement`, `IntersectionLeviDiagonalCharacterProof`, `IntersectionLeviDiagonalCharacterStatement`, `IntersectionLeviModulusBalance`, `IntersectionTransport`, `MonotoneBlocksProof`, `MonotoneBlocksStatement`, `OrbitRepresentatives`, `OrbitRestriction`, `OrbitSectionExtensionProof`, `OrbitSectionExtensionStatement`, `PadicCorrectionCancellationProof`, `PadicCorrectionCancellationStatement`, `PadicParabolicBruhatProof`, `ParabolicOrbitCoefficientComparison`, `ParabolicOrbitCompactComparison`, `ParabolicOrbitComparisonData`, `ParabolicOrbitHaarComparison`, `ParabolicOrbitHaarRatio`, `ParabolicOrbitHaarTransport`, `ParabolicOrbitInductionTransport`, `ParabolicOrbitJacquet`, `ParabolicOrbitJacquetProof`, `ParabolicOrbitJacquetStatement`, `ParabolicOrbitMeasureData`, `ParabolicOrbitNestedAction`, `ParabolicOrbitNormalization`, `ParabolicOrbitNormalizedCoefficient`, `ParabolicOrbitSectionComparison`, `ParabolicOrbitStagesCoefficient`, `ParabolicSupportFiltration`, `ParabolicSupportGradedProof`, `ParabolicSupportGradedStatement`, `ParabolicSupportJacquetProof`, `ParabolicSupportJacquetStatement`, `ParabolicSupportTransport`, `RefinedPositiveCharacter`, `RefinementDefinitions`, `RefinementFunctors`, `RefinementUniqueness`, `SmoothSupportFiltration`, `StandardIntersectionsProof`, `WeylDefinitions`, `WeylMinimalRepresentativeProof`, `WeylStatement`, `WeylUniquenessProof`, `WeylUniquenessStatement`.
- `Langlands.Representation.Hecke`: `ActionIntegrand`, `ActionLocalUnits`, `ActionProjection`, `AntiPullback`, `CommonInvarianceProof`, `CommonInvarianceStatement`, `Convolution`, `Corner`, `CornerAction`, `CornerDetermination`, `DoubleCoset`, `DoubleCosetSandwich`, `FiniteRankAction`, `IntegratedAction`, `IntegratedConvolution`, `NormalizedIndicator`, `SmoothTranspose`, `TestFunction`.
- `Langlands.Representation.Induction`: `BinaryPositiveCompact`, `BinaryProduct`, `BinaryProductConstituentExtraction`, `BinaryProductSubquotients`, `BlockEquivalence`, `BlockFactors`, `CharacterTwistProof`, `CompactAutomorphism`, `CompactAutomorphismIntegralProof`, `CompactAutomorphismIntegralStatement`, `CompactCoinvariantBijectivityProof`, `CompactCoinvariantBijectivityStatement`, `CompactCoinvariantIntegral`, `CompactCoinvariantLocalInverseProof`, `CompactCoinvariantLocalInverseStatement`, `CompactLocalSection`, `CompactLocalSectionSpanningProof`, `CompactLocalSectionSpanningStatement`, `CompactLocallyConstant`, `CompactQuotientCutoff`, `CompactQuotientProof`, `CompactSurjectivityProof`, `CompactSurjectivityStatement`, `CompactTransitivityProof`, `CompactTransitivityStatement`, `ConjugateParabolic`, `Definitions`, `EmptyProductUnit`, `Equivalences`, `FiniteProductTensor`, `FiniteProductTensorBijectiveProof`, `FiniteProductTensorBijectiveStatement`, `HeadTailBinaryProduct`, `HeterogeneousConstruction`, `HeterogeneousPairs`, `InverseTranspose`, `NormalCoinvariantKernelProof`, `NormalCoinvariantKernelStatement`, `NormalCoinvariantMap`, `NormalCoinvariantProof`, `NormalCoinvariantStatement`, `NormalSplitComparison`, `OppositeParabolic`, `Parabolic`, `SingleBlock`, `SplitKernelCharacter`, `SplitKernelCharacterExtension`, `SplitKernelCompact`, `SplitKernelCovariance`, `SplitKernelEquivariant`, `SplitKernelHaarTrivial`, `SplitKernelIntegral`, `SplitKernelLocalizationData`, `SplitKernelSectionAction`, `SplitQuotientProof`, `SplitQuotientStatement`, `SplitStagesCharacterComparison`, `SplitStagesCharacterComparisonStatement`, `SplitStagesCharacterIntegrand`, `SplitStagesComparison`, `SplitStagesRetraction`, `StructuralStatement`, `SurjectivityProof`, `SurjectivityStatement`.
- `Langlands.Representation.Jacquet`: `BlockCompressionProof`, `BlockCompressionStatement`, `BlockPowerKernelProof`, `CanonicalLiftBijectivityProof`, `CanonicalLiftDefinitions`, `CanonicalLiftStatement`, `CharacterAveraging`, `CharacterTwistEquiv`, `Coinvariants`, `CompressionStabilizationProof`, `CompressionStabilizationStatement`, `ExactProof`, `ExactStatement`, `Localization`, `LocalizationExactnessProof`, `LocalizationExactnessStatement`, `LocalizationTransport`, `Normalized`, `Parabolic`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`, `ModuloCenter`.
- `Langlands.Representation.Mirabolic`: `LeftMixedProductSuccessor`, `MixedProducts`.
- `Langlands.Representation.Parabolic`: `AdmissibilityStatement`, `ComposedFunctors`, `ExactnessReciprocityStatement`, `FlattenedJacquetComparisonProof`, `FlattenedJacquetComparisonStatement`, `FlattenedJacquetQuotientProof`, `FlattenedJacquetQuotientStatement`, `FlattenedProductInduction`, `FlattenedRefinementModulusCalculation`, `FlattenedTensorOccurrences`, `GeometricPrerequisitesStatement`, `HeadTailProductInduction`, `InducedMapSurjectivity`, `InductionExactnessProof`, `InductionFactorMatchingProof`, `InductionFactorMatchingStatement`, `InductionFiltration`, `InductionSubrepresentation`, `JacquetFiniteGenerationProof`, `JacquetFiniteGenerationStatement`, `LeviBridges`, `LeviInflationAdmissibilityProof`, `NaturalFirstAdjointness`, `NormalizedAdmissibilityProof`, `NormalizedInductionStatement`, `NormalizedJacquetAdmissibilityProof`, `NormalizedJacquetExactnessProof`, `NormalizedJacquetStatement`, `OppositeJacquetMap`, `OppositeRefinementDefinitions`, `OppositeRefinementFunctors`, `OrderedProductRegroupingEquivalence`, `OrderedProductRegroupingProof`, `OrderedProductRegroupingStatement`, `OrderedRefinementInduction`, `OrderedRefinementTensorInduction`, `ProductInductionFiltration`, `ProductInductionSubrepresentation`, `QuotientCompactProof`, `RefinedInductionAdmissibility`, `RefinedInductionTensorMap`, `RefinedInductionTensorNormalization`, `RefinedInductionTensorProof`, `RefinedInductionTensorStatement`, `RefinedJacquetTensor`, `RefinedOppositeJacquetTensor`, `RefinedTensorOccurrences`, `RefinementCharacter`, `RefinementComposition`, `RefinementCoordinatesNormalizationProof`, `RefinementCoordinatesNormalizationStatement`, `RefinementInductionTransitivityProof`, `RefinementJacquetTransitivityProof`, `RefinementPreimage`, `RefinementTransitivityStatement`, `RegroupingFactorEquivalences`, `ThreeBlockCarrierComparison`, `ThreeBlockInductionAssociativityStatement`, `ThreeBlockRefinementGeometry`, `ThreeBlockRegroupingAssembly`, `ThreeBlockUniverseReduction`, `UnipotentFiniteContainment`.
- `Langlands.Representation.RankinSelberg`: `AnalyticStatement`, `FunctionalEquationStatement`, `GeneralLinearUnimodularity`, `HaarSymmetriesProof`, `HaarSymmetriesStatement`, `LastRowCompactOrbitProof`, `LastRowCompactOrbitStatement`, `Measures`, `QuotientIntegrals`, `RationalContinuation`, `RationalZeta`, `UnimodularityStatement`, `UnipotentUnimodularity`, `ZeroRowLastRowCutoffProof`, `ZeroRowLastRowCutoffStatement`.
- `Langlands.Representation.Schur`: `CountableDimensionProof`, `CountableDimensionStatement`.
- `Langlands.Representation.Shahidi`: `Geometry`, `Induction`, `TwoBlocks`.
- `Langlands.Representation.Smooth`: `Definitions`, `FiniteLengthGrothendieck`, `SmallRealizationProof`, `SmallRealizationStatement`.
- `Langlands.Representation.Smooth.Admissibility`: `CofinalProof`, `CofinalStatement`, `EmbeddingProof`, `EmbeddingStatement`, `EquivalenceProof`, `EquivalenceStatement`, `ExactProof`, `ExactStatement`, `FiniteLengthProof`, `FiniteLengthStatement`.
- `Langlands.Representation.Smooth.Contragredient`: `AdmissibleDualityProof`, `AdmissibleDualityStatement`, `CompactDualityProof`, `CompactDualityStatement`, `Definitions`, `ExactProof`, `ExactStatement`, `FixedVectorsDefinitions`, `GelfandKazhdanAssembly`, `GelfandKazhdanProof`, `GelfandKazhdanStatement`, `HomDualityProof`, `HomDualityStatement`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Smooth.Factorization`: `MultiplicityDefinitions`, `TwoFactorExistenceProof`, `TwoFactorStatement`.
- `Langlands.Representation.Smooth.FixedVectors`: `Definitions`, `FiniteTypes`, `FiniteTypesStatement`, `LawsProof`, `LawsStatement`, `OrderProof`, `OrderStatement`.
- `Langlands.Representation.Smooth.Schur`: `Proof`, `Statement`.
- `Langlands.Representation.Smooth.SmoothPart`: `BasicProof`, `BasicStatement`, `Definitions`, `FixedVectorsDefinitions`.
- `Langlands.Representation.Smooth.Transfer`: `GroupEquivalence`, `PullbackProof`, `PullbackStatement`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Tensor`: `CharacterLocalization`, `CoinvariantReflection`, `ExternalFiltration`, `ExternalMapSurjectivityProof`, `ExternalMapSurjectivityStatement`, `ExternalSubquotient`, `ExternalSubrepresentation`, `FactorMatchingProof`, `FactorMatchingStatement`, `Filtration`, `Finite`, `FiniteEquivalences`, `FiniteFiltration`, `FiniteProperties`, `FiniteRegrouping`, `FlattenedGLRefinement`, `GLRefinement`, `OneFactor`, `SmoothSubquotients`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `LeviComplexPower`, `LeviRealPower`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Unitary`: `Basic`.
- `Langlands.Representation.Unramified`: `Eigenvalues`, `HeckeOperators`, `PrincipalSeries`, `SphericalClassificationStatement`, `SphericalConstituentExistenceProof`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `BruhatCellDistribution`, `BruhatCellFactorizationProof`, `BruhatCellFactorizationStatement`, `BruhatCellInvarianceProof`, `BruhatCellInvarianceStatement`, `BruhatCellRestrictionVanishingProof`, `BruhatCellRestrictionVanishingStatement`, `BruhatCellVanishingProof`, `BruhatCellVanishingStatement`, `BruhatCompatibleSupportProof`, `BruhatCompatibleSupportStatement`, `BruhatFiberAverage`, `BruhatFiberCharacterCovarianceProof`, `BruhatFiberCharacterCovarianceStatement`, `BruhatHaarMeasureProof`, `BruhatHaarMeasureStatement`, `BruhatOrbitalIntegrationProof`, `BruhatOrbitalIntegrationStatement`, `BundledDualTransport`, `CoefficientDistribution`, `CompatibleMonomialFixedProof`, `CompatibleMonomialFixedStatement`, `CompatibleTorus`, `Distribution`, `DistributionInvarianceProof`, `DistributionInvarianceStatement`, `DualTransform`, `GeneralLinear`, `GeneralizedCoefficient`, `GeneralizedCoefficientDescent`, `GeneralizedCoefficientKernelProof`, `GeneralizedCoefficientKernelStatement`, `GeneralizedCoefficientSeparation`, `GenericDualTransport`, `Iwasawa`, `MultiplicityOneProof`, `MultiplicityOneStatement`.
- `Langlands.Topology`: `CompactNormCharacter`.
- `Langlands.Topology.CompactOpen`: `ConjugationStabilizer`, `NeighborhoodBasis`, `NeighborhoodBasisStatement`.
- `Langlands.Topology.GroupAction`: `FiniteOrbitProof`, `FiniteOrbitStatement`.
- `Langlands.Topology.Nonarchimedean`: `Subgroup`.
- `Langlands.VirtualRepresentation`: `Exact`, `ExactTwist`, `Integral`.
- `Langlands.Weil`: `Algebraic`, `AlgebraicProof`, `Pullback`, `Topology`, `TopologyProof`.
- `Langlands.Weil.Local`: `Assembly`, `DegreeCharacters`, `Parameters`, `ResidueCharacters`.
- `Langlands.Weil.Representation`: `Basic`, `CharacterLine`, `Continuity`, `ContinuityProof`, `Determinant`, `DirectSum`, `Dual`, `DualClasses`, `IsomorphismInvarianceProof`, `OperationClosureProof`, `Operations`, `Predicates`, `Twist`, `TwistClasses`, `TwistProperties`.
- `Langlands.WeilDeligne`: `Basic`, `DirectSum`, `Dual`, `ParameterRelations`, `Parameters`, `Twist`.

### Directly named external roots

- `Lean.Elab.Tactic`: `Omega`.
- `Mathlib`: `Tactic`.
- `Mathlib.Algebra.Algebra`: `Bilinear`, `NonUnitalHom`, `NonUnitalSubalgebra`.
- `Mathlib.Algebra.Algebra.Subalgebra`: `Lattice`.
- `Mathlib.Algebra.BigOperators`: `Fin`, `Finprod`, `Pi`.
- `Mathlib.Algebra.BigOperators.Group.Finset`: `Basic`.
- `Mathlib.Algebra.BigOperators.Group.List`: `Basic`.
- `Mathlib.Algebra.BigOperators.Group.Multiset`: `Basic`.
- `Mathlib.Algebra.BigOperators.GroupWithZero`: `Action`.
- `Mathlib.Algebra.Category.ModuleCat`: `Basic`.
- `Mathlib.Algebra.CharP`: `Basic`.
- `Mathlib.Algebra.DirectSum`: `Module`.
- `Mathlib.Algebra.Exact`: `Basic`.
- `Mathlib.Algebra.Field.Subfield`: `Basic`.
- `Mathlib.Algebra.Group.Action`: `Hom`, `Opposite`.
- `Mathlib.Algebra.Group.Equiv`: `TypeTags`.
- `Mathlib.Algebra.Group.Hom`: `Instances`.
- `Mathlib.Algebra.Group.Pi`: `Lemmas`.
- `Mathlib.Algebra.Group.Subgroup`: `Ker`, `Pointwise`.
- `Mathlib.Algebra.Group.Submonoid`: `Basic`.
- `Mathlib.Algebra.Group.TypeTags`: `Finite`, `Hom`.
- `Mathlib.Algebra.Module`: `Opposite`, `PID`, `ULift`.
- `Mathlib.Algebra.Module.LinearMap`: `FiniteRange`.
- `Mathlib.Algebra.Module.Submodule`: `Map`.
- `Mathlib.Algebra.Order.Archimedean`: `Basic`.
- `Mathlib.Algebra.Order.BigOperators.Group`: `Finset`.
- `Mathlib.Algebra.Polynomial`: `FieldDivision`, `Laurent`, `Lifts`, `Roots`.
- `Mathlib.Algebra.Polynomial.Module`: `AEval`, `FiniteDimensional`.
- `Mathlib.Algebra.Ring`: `GeomSum`.
- `Mathlib.Analysis`: `MeanInequalitiesPow`.
- `Mathlib.Analysis.Complex`: `Basic`, `Cardinality`, `Circle`.
- `Mathlib.Analysis.Complex.Polynomial`: `Basic`.
- `Mathlib.Analysis.Fourier`: `FourierTransform`.
- `Mathlib.Analysis.InnerProductSpace`: `Defs`.
- `Mathlib.Analysis.Matrix`: `MeasurableSpace`, `Normed`.
- `Mathlib.Analysis.Normed.Module`: `FiniteDimension`.
- `Mathlib.Analysis.Normed.Operator`: `BoundedLinearMaps`.
- `Mathlib.Analysis.Normed.Unbundled`: `SpectralNorm`.
- `Mathlib.Analysis.Real`: `Sqrt`.
- `Mathlib.Analysis.SpecialFunctions`: `Sqrt`.
- `Mathlib.Analysis.SpecialFunctions.Complex`: `Circle`.
- `Mathlib.Analysis.SpecialFunctions.Pow`: `Complex`, `NNReal`, `Real`.
- `Mathlib.Analysis.SpecificLimits`: `Basic`.
- `Mathlib.Basic.Complex`: `Basic`.
- `Mathlib.CategoryTheory`: `Skeletal`, `Whiskering`.
- `Mathlib.CategoryTheory.Abelian`: `Subcategory`.
- `Mathlib.CategoryTheory.Discrete`: `Basic`.
- `Mathlib.CategoryTheory.Limits.ConcreteCategory`: `Basic`.
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes`: `Zero`.
- `Mathlib.CategoryTheory.ObjectProperty`: `FullSubcategory`.
- `Mathlib.CategoryTheory.Pi`: `Basic`.
- `Mathlib.CategoryTheory.Products`: `Basic`.
- `Mathlib.Combinatorics.Enumerative`: `Composition`.
- `Mathlib.Data.ENat`: `Basic`, `BigOperators`.
- `Mathlib.Data.Fin`: `Rev`.
- `Mathlib.Data.Fin.Tuple`: `Basic`, `Sort`.
- `Mathlib.Data.Finset`: `NatAntidiagonal`.
- `Mathlib.Data.Fintype`: `EquivFin`, `Quotient`, `Sort`, `Sum`.
- `Mathlib.Data.Int`: `Interval`, `LeastGreatest`.
- `Mathlib.Data.Int.Cast`: `Lemmas`.
- `Mathlib.Data.List`: `Pairwise`.
- `Mathlib.Data.Matrix`: `Basic`, `Block`.
- `Mathlib.Data.Nat`: `Find`.
- `Mathlib.Data.PNat`: `Basic`.
- `Mathlib.Data.Set`: `Card`.
- `Mathlib.Data.Set.Finite`: `Basic`.
- `Mathlib.Data.Sym`: `Basic`.
- `Mathlib.Data.ZMod`: `Basic`.
- `Mathlib.FieldTheory`: `AbsoluteGaloisGroup`, `PrimitiveElement`.
- `Mathlib.FieldTheory.Finite`: `Basic`, `Extension`.
- `Mathlib.FieldTheory.Galois`: `Profinite`.
- `Mathlib.FieldTheory.RatFunc`: `AsPolynomial`.
- `Mathlib.GroupTheory`: `DoubleCoset`, `FiniteIndexNormalSubgroup`, `Index`, `OrderOfElement`, `Transfer`.
- `Mathlib.GroupTheory.Abelianization`: `Defs`.
- `Mathlib.GroupTheory.Coset`: `Defs`.
- `Mathlib.GroupTheory.GroupAction`: `Basic`, `ConjAct`, `Defs`, `Quotient`.
- `Mathlib.GroupTheory.QuotientGroup`: `Defs`.
- `Mathlib.GroupTheory.Subgroup`: `Centralizer`.
- `Mathlib.LinearAlgebra`: `AnnihilatingPolynomial`, `Determinant`, `Isomorphisms`, `Projection`, `Semisimple`, `Trace`.
- `Mathlib.LinearAlgebra.AffineSpace`: `AffineMap`.
- `Mathlib.LinearAlgebra.Basis`: `VectorSpace`.
- `Mathlib.LinearAlgebra.BilinearForm`: `Properties`.
- `Mathlib.LinearAlgebra.Charpoly`: `Basic`, `ToMatrix`.
- `Mathlib.LinearAlgebra.Dimension`: `Basic`, `Constructions`, `StrongRankCondition`.
- `Mathlib.LinearAlgebra.DirectSum`: `Finite`.
- `Mathlib.LinearAlgebra.Dual`: `Defs`, `Lemmas`.
- `Mathlib.LinearAlgebra.Eigenspace`: `Basic`, `Pi`, `Triangularizable`.
- `Mathlib.LinearAlgebra.FiniteDimensional`: `Basic`, `Defs`, `Lemmas`.
- `Mathlib.LinearAlgebra.Finsupp`: `LinearCombination`, `VectorSpace`.
- `Mathlib.LinearAlgebra.FreeModule.Finite`: `Matrix`.
- `Mathlib.LinearAlgebra.Matrix`: `BilinearForm`, `Block`, `Diagonal`, `ElementaryRowOperations`, `Kronecker`, `NonsingularInverse`, `Permutation`, `Rank`, `Reindex`, `SchurComplement`, `Transvection`.
- `Mathlib.LinearAlgebra.Matrix.Charpoly`: `Basic`, `Coeff`, `Univ`.
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup`: `Basic`, `Defs`.
- `Mathlib.LinearAlgebra.PiTensorProduct`: `Basic`, `Basis`, `Finite`, `Generators`.
- `Mathlib.LinearAlgebra.Quotient`: `Basic`.
- `Mathlib.LinearAlgebra.TensorProduct`: `Basis`, `Finiteness`, `RightExactness`.
- `Mathlib.Logic.Equiv.Fin`: `Basic`.
- `Mathlib.MeasureTheory.Constructions`: `Pi`.
- `Mathlib.MeasureTheory.Function`: `LocallyIntegrable`, `SimpleFunc`.
- `Mathlib.MeasureTheory.Function.LpSeminorm`: `Defs`.
- `Mathlib.MeasureTheory.Group`: `Integral`, `LIntegral`, `MeasurableEquiv`, `Measure`, `ModularCharacter`.
- `Mathlib.MeasureTheory.Integral`: `Marginal`, `Prod`.
- `Mathlib.MeasureTheory.Integral.Bochner`: `Basic`, `ContinuousLinearMap`, `Set`.
- `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani`: `Real`.
- `Mathlib.MeasureTheory.Measure`: `Prod`, `Regular`.
- `Mathlib.MeasureTheory.Measure.Haar`: `Basic`, `DistribChar`, `MulEquivHaarChar`, `Unique`.
- `Mathlib.MeasureTheory.Measure.Lebesgue`: `Basic`.
- `Mathlib.MeasureTheory.Measure.Typeclasses`: `Finite`.
- `Mathlib.NumberTheory.LocalField`: `Basic`.
- `Mathlib.NumberTheory.Padics`: `LocalField`, `RingHoms`.
- `Mathlib.Order`: `Atoms`, `WithBot`.
- `Mathlib.Order.Hom`: `Set`.
- `Mathlib.Order.Interval.Finset`: `Fin`.
- `Mathlib.Order.Interval.Set`: `Infinite`.
- `Mathlib.RepresentationTheory`: `Basic`, `Coinduced`, `Coinvariants`, `Equiv`, `Intertwining`, `Invariants`, `Irreducible`, `Semisimple`, `Subrepresentation`.
- `Mathlib.RepresentationTheory.Rep`: `Basic`, `Res`.
- `Mathlib.RingTheory`: `AdjoinRoot`, `FiniteLength`, `Length`, `Nakayama`, `PowerBasis`, `PrincipalIdealDomain`.
- `Mathlib.RingTheory.Adjoin`: `Basic`.
- `Mathlib.RingTheory.Adjoin.Polynomial`: `Basic`.
- `Mathlib.RingTheory.Algebraic`: `LinearIndependent`.
- `Mathlib.RingTheory.Artinian`: `Module`.
- `Mathlib.RingTheory.DedekindDomain`: `IntegralClosure`.
- `Mathlib.RingTheory.Finiteness`: `Basic`, `Defs`, `Finsupp`.
- `Mathlib.RingTheory.Flat`: `Basic`.
- `Mathlib.RingTheory.FractionalIdeal`: `Operations`.
- `Mathlib.RingTheory.Ideal.Quotient`: `Basic`, `Operations`.
- `Mathlib.RingTheory.Localization`: `Ideal`.
- `Mathlib.RingTheory.Nilpotent`: `Basic`.
- `Mathlib.RingTheory.Noetherian`: `Basic`, `Defs`.
- `Mathlib.RingTheory.Norm`: `Transitivity`.
- `Mathlib.RingTheory.Polynomial`: `Basic`, `UniqueFactorization`.
- `Mathlib.RingTheory.RamificationInertia`: `Basic`.
- `Mathlib.RingTheory.SimpleModule`: `Basic`.
- `Mathlib.RingTheory.Trace`: `Basic`.
- `Mathlib.RingTheory.Valuation`: `Extension`, `Integral`, `LocalSubring`, `RamificationGroup`.
- `Mathlib.Tactic`: `Group`, `Linarith`, `NoncommRing`, `NormNum`.
- `Mathlib.Topology`: `Bases`, `LocallyClosed`, `UrysohnsLemma`.
- `Mathlib.Topology.Algebra`: `ClopenNhdofOne`, `ConstMulAction`, `Constructions`, `ContinuousMonoidHom`, `Field`, `GroupWithZero`, `MulAction`, `MvPolynomial`, `OpenSubgroup`, `Support`.
- `Mathlib.Topology.Algebra.Category.ProfiniteGrp`: `Basic`, `Completion`.
- `Mathlib.Topology.Algebra.Group`: `Basic`, `ClosedSubgroup`, `Matrix`, `Neighborhood`, `OpenMapping`, `Pointwise`, `Quotient`, `Subgroup`, `Units`.
- `Mathlib.Topology.Algebra.Module`: `FiniteDimension`, `ModuleTopology`.
- `Mathlib.Topology.Algebra.Nonarchimedean`: `Basic`, `TotallyDisconnected`.
- `Mathlib.Topology.Algebra.ProperAction`: `Basic`.
- `Mathlib.Topology.Algebra.Ring`: `Compact`, `Ideal`.
- `Mathlib.Topology.Algebra.ValuativeRel`: `ValuativeTopology`.
- `Mathlib.Topology.Algebra.Valued`: `NormedValued`.
- `Mathlib.Topology.Baire`: `Lemmas`, `LocallyCompactRegular`.
- `Mathlib.Topology.Compactness`: `Compact`, `LocallyCompact`, `SigmaCompact`.
- `Mathlib.Topology.Connected`: `TotallyDisconnected`.
- `Mathlib.Topology.ContinuousMap`: `CompactlySupported`.
- `Mathlib.Topology.Homeomorph`: `Defs`, `Lemmas`, `Quotient`.
- `Mathlib.Topology.Instances`: `Int`, `Matrix`.
- `Mathlib.Topology.Instances.NNReal`: `Lemmas`.
- `Mathlib.Topology.Instances.Real`: `Lemmas`.
- `Mathlib.Topology.LocallyConstant`: `Algebra`, `Basic`.
- `Mathlib.Topology.MetricSpace.Ultra`: `TotallySeparated`.
- `Mathlib.Topology.Order`: `Compact`.
- `Mathlib.Topology.Separation`: `Profinite`.
