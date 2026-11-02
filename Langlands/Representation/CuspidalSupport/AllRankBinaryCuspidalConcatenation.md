# Actual cuspidal concatenation in all ranks

Author: Worker 357.

This module constructs actual cuspidal data and actual supplied supercuspidal
representatives for the normalized binary product of two cuspidal inductions,
for arbitrary natural ranks. It proves the rank sum, length, compatibility
with the original representation witnesses, literal addition of the multisets,
and an actual smooth-category isomorphism. Repetitions and independent field
and factor universes are retained.

## Parameters and returned data

All declarations are in
`Langlands.PadicField.TopologicalData.BinaryCuspidalConcatenation`. Fix arbitrary
`p` with `Fact p.Prime`, `F : PadicField.{uF} p`, the supplied
`T : F.TopologicalData`, natural numbers `k,l,a,b`, and families

```lean
ρ : Fin k → CuspidalDatum.{uV, uF} T
τ : Fin l → CuspidalDatum.{uV, uF} T
```

with rank-sum equalities `hρ : ∑ i, (ρ i).rank = a` and
`hτ : ∑ i, (τ i).rank = b`. The supplied actual families are

```lean
A : ∀ i, SupercuspidalRep.{uF, uV}
  (F := F.Carrier) (n := (ρ i).rank)
C : ∀ i, SupercuspidalRep.{uF, uV}
  (F := F.Carrier) (n := (τ i).rank)
```

using the topology supplied by `T`. No positivity of `a,b`, distinctness,
ordering, linkage, admissibility of an induced object, finite length or
irreducibility of an induced product is assumed.

`AllRankData ρ τ hρ hτ A C` is a structure with the following fields:

- `count : ℕ` and `family : Fin count → CuspidalDatum.{uV,uF} T`;
- `rank_sum : ∑ i, (family i).rank = a+b`;
- `representatives`, actual `SupercuspidalRep.{uF,uV}` objects on those ranks;
- `represents`, which takes the original witnesses that `A,C` represent
  `ρ,τ` and proves that the returned representatives represent `family`;
- `count_eq : count = k+l`;
- `multiset_eq`, the literal equality
  `(List.ofFn family : Multiset _) = (List.ofFn ρ : Multiset _) +
  (List.ofFn τ : Multiset _)`;
- `productIso`, an actual isomorphism from
  `T.cuspidalProductInduced family rank_sum representatives` to
  `(T.binaryNormalizedProductFunctor a b).obj
  (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C)`.

`allRank ρ τ hρ hτ A C` constructs this structure. The data and original
representatives stay in `uV`; there is no universe-lifted replacement of a
cuspidal datum or supplied supercuspidal representation. Each original
cuspidal induction has carrier universe `max uF uV`. The binary functor at
that input universe has output universe `max uF (max uF uV)`, definitionally
`max uF uV`, matching the returned cuspidal induction. Declaration inspection
retains exactly the independent level parameters `uF,uV` and only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Empty families and exact rank comparison

`length_eq_zero_of_rank_sum_zero` proves that a cuspidal family of total rank
zero has length zero. Each datum rank is positive. The actual cuspidal shape
is therefore a `BlockShape 0`, whose index type is empty by the published
`BlockShape.isEmpty_blockIndex_rankZero`: an index would supply an element of
`Fin 0` from the first coordinate in its positive block. If the original
length were positive, its index zero would contradict this emptiness.
`multiset_eq_zero_of_rank_sum_zero` substitutes the resulting length equality
and simplifies the empty list multiset.

The private `cuspidalRankEquiv` takes rank-sum witnesses `hm,hn` for the same
supplied family and an equality `h : n = m`. It compares the induction at
rank `n` with the induction at rank `m` precomposed by the precise homomorphism

```lean
(GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom
```

from `GL_n` to `GL_m`. Its proof eliminates `h`, uses the published identity
law for this matrix reindexing, and takes the identity representation
equivalence. Proof irrelevance identifies the rank-sum witnesses after equality
elimination. The helper retains the supplied field, topology and representatives.

## Actual zero-rank unit isomorphisms

`leftZeroProductIso` accepts `hρ : ∑ i, (ρ i).rank = 0` and the arbitrary
right family with rank sum `b`. Its source is precisely the right cuspidal
induction with rank-sum witness `hτ.trans (Nat.zero_add b).symm`, so its
ambient group is `GL_(0+b)`. Its target is the literal binary functor applied
to both original cuspidal inductions, of ranks `0,b`.

The proof first uses the published `emptyProductUnitIso` on the actual left
cuspidal shape and its actual representatives. This identifies that specific
empty induction with `T.binaryProductUnit.{uF,max uF uV}`. Mapping this
isomorphism and the identity on the right object through the binary functor
gives an isomorphism to the product with the scalar unit. The published
`binaryProductLeftUnitEquiv` identifies that product with the lift of the
right action pulled back along
`GeneralLinear.reindex (finCongr (Nat.zero_add b))`. Composing with the inverse
of `BinaryTensor.liftEquiv` removes this carrier lift. Finally the private
rank comparison above identifies the source induction with the same pulled
back action. Composing in the appropriate inverse directions and applying
`SmoothRep.mkIso` yields the displayed isomorphism.

`rightZeroProductIso` uses the same construction with the actual right empty
induction, `binaryProductRightUnitEquiv`, and the exact reindexing along
`Nat.add_zero a`. Its source retains the original left family and original
representatives, with rank-sum witness `hρ.trans (Nat.add_zero a).symm`.
Neither proof treats an arbitrary smooth `GL_0` carrier as the scalar unit;
the unit identification is supplied for the actual induction of the empty
family.

The published empty-product proof evaluates the actual induced function at
identity, with inverse the constant function, since `GL_0` is trivial and its
parabolic is the whole group. It then uses the actual empty indexed tensor
product's scalar equivalence and `ULift.moduleEquiv`. The binary unit proof
uses the actual zero-rank tensor model followed by the scalar tensor unit
map. These are proved maps with both inverse and intertwining laws.

## The all-rank construction

`allRank` splits first on `a=0`, then on `b=0`, matching the existing binary
product's rank cases.

If `a=0`, it returns `count=l`, exactly `family=τ`, exactly the original
representatives `C`, and the left zero-rank product isomorphism. The empty
left family has `k=0` and zero multiset, which prove the length and multiset
fields. The representation compatibility field is the original right
compatibility witness. This branch includes `a=b=0`.

If `a` is nonzero and `b=0`, it returns `count=k`, the original family `ρ`
and representatives `A`, and the right zero-rank product isomorphism. The
right family's zero length and zero multiset prove the other fields.

If both ranks are nonzero, natural-number positivity permits reuse of the
published [BinaryCuspidalConcatenation](BinaryCuspidalConcatenation.md).
The returned length is the length of its flattened binary refinement; its
family and representatives are exactly `flattenedFamily` and
`flattenedRepresentatives`. The rank, length, representation compatibility,
multiset equality and product isomorphism are the corresponding published
results. Those representatives are the original supplied objects listed
by the inverse consecutive block equivalence. The multiset identity sums
singletons and reindexes finite sums, so every repetition remains counted.
There is no replacement by a set or a multiplicity-free list.

## Provenance and dependency audit

This is an internal construction from independently accepted, published actual
induction and tensor maps and elementary finite-index algebra. It introduces
no new assertion from the literature and needs no source tuple. Its direct
imports are the published positive binary cuspidal concatenation and
[EmptyProductUnit](../Induction/EmptyProductUnit.md). It changes neither pair.

The positive branch reuses general normalized induction in stages through
`Parabolic.flattenedProductInducedEquiv`. Its implemented lower route uses the
actual ordered-refinement equivalence: evaluation at the inner identity,
its inverse with the inverse positive half-modulus, exact consecutive block
coordinates, indexed tensor regrouping and the proved pointwise induction
and tensor bijectivity. The bijectivity proof uses finite sums of compact
open double-coset sections on compact parabolic quotients. Its injectivity
uses tensor fixed-vector inclusions and evaluations. The coordinate
normalization identifies the actual shapes and their modulus characters.
It does not use a segment, head, socle or classification conclusion.

The zero branches add only the actual empty-product comparison described
above, functoriality, actual scalar tensor unit maps, the existing lift
equivalence, equality elimination and categorical composition. The definitions
of cuspidal shape, cuspidal induction and representation of a datum come
from `Classification.SupercuspidalSupport`. No existence or uniqueness theorem
for supercuspidal support is assumed.

The recursive import inventory below was checked against Library commit
`3c99509d9f7a41b5f3932da0e3877264b3a70a9e`. It contains 405 project modules,
including this new pair, and 175 direct external import roots. All inherited
Lean/Markdown pairs are present, nonempty and byte-identical to that Library.
There are no missing project imports, proof holes, imports of pending
candidates or matches for the audited excluded names and task identifiers.
The lexical scan removes comments and strings. The external inventory lists
direct external roots, not the recursive Mathlib closure.

The broader inherited closure includes the lower cuspidal/Jacquet,
finite-length and tensor-occurrence infrastructure inventoried below. The
18 Classification modules provide definitions, statement interfaces and
general lower results. The actual construction above invokes none of the
excluded segment/head/socle, full segment Jacquet or classification
conclusions. `FlattenedTensorOccurrences` is not used as a mathematical
input here. The four derivative-named modules are only
`MirabolicMinusExactnessStatement`, `MirabolicMinus`, `MirabolicCharacter`
and `ShortExactFunctorLaws`; no segment derivative formula or other derivative
conclusion is used. This argument records the actual proof route as well
as its imports; a name scan alone does not establish independence.

The host's Independence exclusions remain unchanged. The trusted operator
responses [bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md),
and [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
were read in full. This construction needs no segment derivative permission.
Its proof uses none of Ze80 3.5/9.6 or their proof successors, the segment-socle
part of task `8e5b4563-0365-41c7-b134-70f2a0b36292`, the host criterion in either direction, or any
conclusion of tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5`,
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`, `30341ae4-65f2-4a0e-9283-763db01a409e`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`8252833d-c269-41a9-824c-5879e531b23b`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, or
`bf433f0a-921a-428c-b0c0-6475438125ac`.

## Remaining scope

The structure provides data and an actual product comparison, including all
rank-zero cases. It proves no irreducibility, finite length, support
classification, support-only derivative truncation bound, product derivative
aggregation, nonlinkage survival or linked converse. Both directions of the
host `SegmentHeadProductIrreducibility` criterion remain to be proved.

## Recursive project inventory

```text
Langlands.Algebra.CommutingDimensionHelpers
Langlands.Algebra.CommutingDimensionNilpotent
Langlands.Algebra.CommutingDimensionNumerics
Langlands.Algebra.CommutingDimensionPrimary
Langlands.Algebra.CommutingDimensionRecurrence
Langlands.Algebra.MultisetOfFn
Langlands.Algebra.SandwichDimensionBoundProof
Langlands.Algebra.SandwichDimensionBoundStatement
Langlands.Algebra.SeparatedMatrixRepresentations
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockContractionProof
Langlands.Group.GL.BlockContractionStatement
Langlands.Group.GL.BlockIwahoriBasis
Langlands.Group.GL.BlockIwahoriBasisStatement
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockUnipotent
Langlands.Group.GL.Blocks
Langlands.Group.GL.CartanProof
Langlands.Group.GL.CartanStatement
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.DominantExponentGeneration
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
Langlands.Group.GL.PrincipalBlockFactorizationProof
Langlands.Group.GL.PrincipalBlockFactorizationStatement
Langlands.Group.GL.PrincipalLevelDominance
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.RefinementCoordinates
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.SingletonBlocks
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperUnipotent
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalField.Canonical
Langlands.LocalField.CanonicalProof
Langlands.LocalField.CanonicalStatement
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Basic
Langlands.Representation.Category.ClassInvariants
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.CanonicalConstituents
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.FiniteLengthProof
Langlands.Representation.Classification.FiniteLengthStatement
Langlands.Representation.Classification.RelativeGenericityStatement
Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
Langlands.Representation.Classification.RelativeRegularComparisonStatement
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TemperedInductionStatement
Langlands.Representation.Classification.TemperedSupportStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.CompactCoefficient.AdmissibleComplement
Langlands.Representation.CompactCoefficient.AdmissibleLifting
Langlands.Representation.CompactCoefficient.AdmissibleRetraction
Langlands.Representation.CompactCoefficient.AmbientProjector
Langlands.Representation.CompactCoefficient.Classes
Langlands.Representation.CompactCoefficient.ConditionalProjection
Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
Langlands.Representation.CompactCoefficient.GroupTransport
Langlands.Representation.CompactCoefficient.Isotypic
Langlands.Representation.CompactCoefficient.IsotypicTransport
Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
Langlands.Representation.CompactCoefficient.SemisimplicityProof
Langlands.Representation.CompactCoefficient.SemisimplicityStatement
Langlands.Representation.CompactCoefficient.TotalCompactness
Langlands.Representation.CompactCoefficient.TotalProjector
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Conductor.Definitions
Langlands.Representation.Conductor.PrincipalCongruence
Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport.AllRankBinaryCuspidalConcatenation
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
Langlands.Representation.CuspidalSupport.AssociationForwardStatement
Langlands.Representation.CuspidalSupport.AssociationLawsProof
Langlands.Representation.CuspidalSupport.AssociationLawsStatement
Langlands.Representation.CuspidalSupport.AssociationReduction
Langlands.Representation.CuspidalSupport.BinaryCuspidalConcatenation
Langlands.Representation.CuspidalSupport.BlockMap
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
Langlands.Representation.CuspidalSupport.DeterminantUnit
Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement
Langlands.Representation.CuspidalSupport.DualAveraging
Langlands.Representation.CuspidalSupport.FiniteBlockShapes
Langlands.Representation.CuspidalSupport.GroupTransport
Langlands.Representation.CuspidalSupport.HarishChandraAssembly
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement
Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement
Langlands.Representation.CuspidalSupport.HarishChandraForwardProof
Langlands.Representation.CuspidalSupport.HarishChandraStatement
Langlands.Representation.CuspidalSupport.InducedJacquetCount
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.JacquetLengthDetector
Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement
Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviAssociation
Langlands.Representation.CuspidalSupport.LeviCompactPart
Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.LeviGapVanishing
Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
Langlands.Representation.CuspidalSupport.LeviSplitContraction
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
Langlands.Representation.CuspidalSupport.PointwiseProjectorSum
Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof
Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof
Langlands.Representation.CuspidalSupport.RefinedJacquetLengthStatement
Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.ShortExactFunctorLaws
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.Central
Langlands.Representation.Exponents.ComplexTwistFamilies
Langlands.Representation.Exponents.DualJacquet
Langlands.Representation.Exponents.DualJacquetStatement
Langlands.Representation.Exponents.Jacquet
Langlands.Representation.Exponents.NilpotenceIndex
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Exponents.RealTwistFamilies
Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement
Langlands.Representation.Exponents.WeylBranchPiecesStatement
Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
Langlands.Representation.Filtration.ActualGradedExtraction
Langlands.Representation.Filtration.CoarseJacquetExtraction
Langlands.Representation.Filtration.CoarseJacquetFactorization
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.ExactConstituentExtraction
Langlands.Representation.Filtration.ExactSmoothSubquotients
Langlands.Representation.Filtration.ExactSmoothTransport
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.MultiplicityStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Filtration.SmoothGradedObject
Langlands.Representation.Filtration.SubquotientAlgebraProof
Langlands.Representation.Filtration.SubquotientAlgebraStatement
Langlands.Representation.Filtration.SubsingletonProof
Langlands.Representation.Filtration.VanishingStatement
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.GeometricLemmaStatement
Langlands.Representation.Geometric.IntersectionTransport
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
Langlands.Representation.Hecke.ActionIntegrand
Langlands.Representation.Hecke.ActionProjection
Langlands.Representation.Hecke.CommonInvarianceProof
Langlands.Representation.Hecke.CommonInvarianceStatement
Langlands.Representation.Hecke.Convolution
Langlands.Representation.Hecke.Corner
Langlands.Representation.Hecke.CornerAction
Langlands.Representation.Hecke.DoubleCoset
Langlands.Representation.Hecke.DoubleCosetSandwich
Langlands.Representation.Hecke.IntegratedAction
Langlands.Representation.Hecke.IntegratedConvolution
Langlands.Representation.Hecke.NormalizedIndicator
Langlands.Representation.Hecke.TestFunction
Langlands.Representation.Induction.BinaryProduct
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
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.BlockCompressionProof
Langlands.Representation.Jacquet.BlockCompressionStatement
Langlands.Representation.Jacquet.BlockPowerKernelProof
Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
Langlands.Representation.Jacquet.CanonicalLiftDefinitions
Langlands.Representation.Jacquet.CanonicalLiftStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof
Langlands.Representation.Parabolic.FlattenedJacquetComparisonStatement
Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof
Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement
Langlands.Representation.Parabolic.FlattenedProductInduction
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.FlattenedTensorOccurrences
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.JacquetFiniteGenerationProof
Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement
Langlands.Representation.Parabolic.LeviBridges
Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
Langlands.Representation.Parabolic.NormalizedJacquetStatement
Langlands.Representation.Parabolic.OppositeJacquetMap
Langlands.Representation.Parabolic.OppositeRefinementDefinitions
Langlands.Representation.Parabolic.OppositeRefinementFunctors
Langlands.Representation.Parabolic.OrderedRefinementInduction
Langlands.Representation.Parabolic.OrderedRefinementTensorInduction
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionTensorMap
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorProof
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinedJacquetTensor
Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor
Langlands.Representation.Parabolic.RefinedTensorOccurrences
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Parabolic.RefinementTransitivityStatement
Langlands.Representation.Parabolic.UnipotentFiniteContainment
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EmbeddingProof
Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Admissibility.ExactProof
Langlands.Representation.Smooth.Admissibility.ExactStatement
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.ExactProof
Langlands.Representation.Smooth.Contragredient.ExactStatement
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.HomDualityProof
Langlands.Representation.Smooth.Contragredient.HomDualityStatement
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions
Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
Langlands.Representation.Smooth.Factorization.TwoFactorStatement
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.FixedVectors.FiniteTypes
Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement
Langlands.Representation.Smooth.FixedVectors.LawsProof
Langlands.Representation.Smooth.FixedVectors.LawsStatement
Langlands.Representation.Smooth.FixedVectors.OrderProof
Langlands.Representation.Smooth.FixedVectors.OrderStatement
Langlands.Representation.Smooth.Schur.Proof
Langlands.Representation.Smooth.Schur.Statement
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.GroupEquivalence
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.SubrepresentationLattice
Langlands.Representation.Tensor.CharacterLocalization
Langlands.Representation.Tensor.ExternalSubquotient
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.FlattenedGLRefinement
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Tensor.SmoothSubquotients
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.LeviComplexPower
Langlands.Representation.Twist.LeviRealPower
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
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

## Direct external import roots

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.Algebra.NonUnitalHom
Mathlib.Algebra.Algebra.NonUnitalSubalgebra
Mathlib.Algebra.Algebra.Subalgebra.Lattice
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Group.Multiset.Basic
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Submonoid.Basic
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Matrix.Normed
Mathlib.Analysis.MeanInequalitiesPow
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Combinatorics.Enumerative.Composition
Mathlib.Data.ENat.Basic
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Int.Interval
Mathlib.Data.Matrix.Basic
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.Data.Set.Finite.Basic
Mathlib.Data.ZMod.Basic
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Index
Mathlib.GroupTheory.QuotientGroup.Defs
Mathlib.LinearAlgebra.AffineSpace.AffineMap
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Charpoly.Basic
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.LinearAlgebra.Eigenspace.Pi
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.SchurComplement
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.Projection
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.Finiteness
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.Hom.Set
Mathlib.Order.Interval.Finset.Fin
Mathlib.Order.WithBot
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Equiv
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.Adjoin.Basic
Mathlib.RingTheory.Adjoin.Polynomial.Basic
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Finiteness.Defs
Mathlib.RingTheory.Finiteness.Finsupp
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Length
Mathlib.RingTheory.Nakayama
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.Polynomial.Basic
Mathlib.RingTheory.PowerBasis
Mathlib.RingTheory.PrincipalIdealDomain
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic
Mathlib.Tactic.Group
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.Matrix
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.Instances.Real.Lemmas
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Separation.Profinite
```
