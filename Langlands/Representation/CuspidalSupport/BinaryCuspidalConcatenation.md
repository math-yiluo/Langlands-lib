# Binary concatenation of supplied cuspidal families

Author: Worker 357.

This module constructs the consecutive concatenation of two supplied cuspidal
families of positive total ranks, retains their actual supplied representatives,
and proves that its actual induction is the literal normalized binary product
of the original two inductions. It also proves addition of the multisets of
cuspidal data. Repeated data and independent field/factor universes are retained.
This is internal induction and finite-index algebra, not an irreducibility or
support-classification assertion.

## Parameters and data

All declarations are in
`Langlands.PadicField.TopologicalData.BinaryCuspidalConcatenation`, except the
published inputs used by the proof. Fix arbitrary `p` with `Fact p.Prime`,
`F : PadicField.{uF} p`, the supplied `T : F.TopologicalData`, natural lengths
`k,l`, strictly positive ranks `a,b`, and families

```lean
ρ : Fin k → CuspidalDatum.{uV, uF} T
τ : Fin l → CuspidalDatum.{uV, uF} T
```

with supplied rank-sum equalities `hρ : ∑ j, (ρ j).rank = a` and
`hτ : ∑ j, (τ j).rank = b`. The two positivity proofs are named `ha,hb`.
The universes `uF,uV` remain independent throughout. There is no distinctness,
ordering, linkage or support premise on these families.

`length k l : Fin 2 → ℕ` has values `k,l`. The nested `family ρ τ` has the
original family in its respective outer slot, using the same dependent
`Fin.cases` distinction. `family_rank_sum` proves its rank sum at either slot
equals that slot's size in the published positive binary block shape
`B := BlockShape.binary a b ha hb`.

`refinement ρ τ ha hb hρ hτ` is the refinement `S` of `B` whose slot `i` is
literally the cuspidal shape of `family ρ τ i`, with that rank-sum proof.
In particular its lengths and block sizes are definitionally those of the
original nested cuspidal family, rather than arbitrary isomorphic data.

Let `e := B.flattenBlockEquiv S`. Its domain is the sigma type of an outer
slot and an inner index, and its codomain is the standard consecutive flattened
index type. The declaration `flattenedFamily` lists the original nested data
using `e.symm`. Its domain is exactly `Fin (B.flatten S).length`.
`flattened_length` proves `(B.flatten S).length = k + l`.
`flattenedFamily_rank_sum` proves its total rank is `a+b` using the existing
flattened shape's `sum_eq`. `flattenedFamily_shape` proves that the cuspidal
shape of this flattened family, with this rank-sum witness, equals `B.flatten S`.
The last two proofs are definitional: the inner shapes were defined as the
cuspidal shapes of these very data. The public construction does not require a
chosen cast to `Fin (k+l)`.

## Supplied representatives and multiplicities

The declarations accept arbitrary actual families

```lean
A : ∀ i, SupercuspidalRep.{uF, uV}
  (F := F.Carrier) (n := (ρ i).rank)
C : ∀ i, SupercuspidalRep.{uF, uV}
  (F := F.Carrier) (n := (τ i).rank)
```

for the topology supplied by `T`. `representatives` puts these actual objects
in their corresponding outer slots. `flattenedRepresentatives` lists those
same objects using `e.symm`, with their original carrier universe `uV`.
There is no choice of new representatives or a carrier lift. If `hA,hC` state
that the supplied objects represent the original cuspidal data, then
`flattenedRepresentatives_represents` proves that the flattened objects
represent the flattened data. It checks the same assertion in each outer slot.

`flattenedFamily_multiset` proves the literal multiset equality

```text
(List.ofFn flattenedFamily : Multiset (CuspidalDatum T))
  = (List.ofFn ρ : Multiset (CuspidalDatum T))
      + (List.ofFn τ : Multiset (CuspidalDatum T)).
```

The implemented proof first writes each list's multiset as the finite sum of
its singleton entries; this elementary helper is private. It reindexes the
flattened sum along `e.symm`, applies the finite sigma-sum identity, and reduces
the two outer indices to their original families. It uses multiset addition,
never conversion to a set, so equal data in either family or across the two
families are counted with their original multiplicities.

## Actual induction comparison

`productIso ρ τ ha hb hρ hτ A C` is an actual smooth-category isomorphism from

```lean
T.cuspidalProductInduced (flattenedFamily ρ τ ha hb hρ hτ)
  (flattenedFamily_rank_sum ρ τ ha hb hρ hτ)
  (flattenedRepresentatives ρ τ ha hb hρ hτ A C)
```

to

```lean
(T.binaryNormalizedProductFunctor a b).obj
  (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C)
```

The input objects `A,C` intrinsically are smooth supercuspidal
representations. No extra irreducibility or finite-length assertion about
either induced product, no admissibility premise on an induced object, and no
representation-of-the-data equalities are needed for this isomorphism: the
construction works with these actual objects on their prescribed ranks. The
separate `flattenedRepresentatives_represents` lemma supplies that compatibility
when `hA,hC` are given.

The two original cuspidal inductions have carriers in `max uF uV`. The binary
functor is therefore applied at that input carrier universe; its output is in
`max uF (max uF uV)`, definitionally `max uF uV`, the same universe as the
flattened induction. The original cuspidal data and supplied factors remain
in `uV`. `productEquiv` extracts the underlying actual representation
equivalence, with its inverse and intertwining laws, from this same isomorphism.

The implemented proof is the following composition. Put the supplied smooth
objects into the nested family `D`. The inner inductions form a smooth family
`Z` on the two outer blocks. A finite case split proves `Z` equals the published
binary pair family of the two original cuspidal inductions. Mapping this
family equality through the outer normalized product functor gives an actual
isomorphism from the outer product to the published positive binary product.

The published `Parabolic.flattenedProductInducedEquiv F T B S D` compares the
actual flattened normalized product with the actual outer product of the
inner inductions. A private helper only bundles that existing equivalence in
the smooth category. Another private helper transports a normalized product
along equality of its shape and heterogeneous equality of its supplied family;
it is proved by equality elimination and the identity isomorphism. Applied to
`flattenedFamily_shape` and the definitional equality of the flattened supplied
families, it identifies the source with the existing `cuspidalProductInduced`
object. Finally the inverse of the published
`binaryNormalizedProductPositiveIso` identifies the positive product with the
literal all-rank binary functor at these positive ranks. This composition gives
`productIso`. The helpers are kept private and do not duplicate a public general
flattening theorem.

## Provenance and actual dependency route

This is internal provenance. It specializes published actual constructions and
proves elementary finite-index identities; it introduces no new literature
assertion or source tuple. The relevant published proof bodies were inspected,
in addition to the recursive import scan described below.

`Parabolic.FlattenedProductInduction` uses the published ordered-refinement
comparison with the actual consecutive block equivalence, size equalities and
coordinate identity. Its factor identification cancels this block equivalence
on the original supplied nested objects. `OrderedRefinementTensorInduction`
then uses actual GL tensor regrouping, smooth induction of an equivariant
linear equivalence, proved normalized induction in stages, and the proved
refined tensor/induction comparison.

In `OrderedRefinementInduction` and
`RefinementInductionTransitivityProof`, the forward map evaluates the inner
induced function at identity. The inverse evaluates the direct section at the
actual Levi embedding and multiplies by the inverse outer positive half-modulus.
The proofs verify covariance, a uniform open stabilizer, both inverse laws and
naturality on the existing induced spaces. The coordinate-normalization proof
identifies the actual ordered shapes and their full modulus characters, takes
their canonical positive square roots, and uses the identity conjugator on
actual functions. It does not postulate induction transitivity or change the
normalizing character.

`RefinedInductionTensorProof` obtains the actual pointwise map's bijectivity
from `FiniteProductTensorBijectiveProof`, the proved compactness of parabolic
quotients, and the local-field topology supplied by `T`. The finite-product
proof constructs compact double-coset sections at a compact open level.
Finite sums of those sections give surjectivity; tensor fixed-vector inclusions
and evaluation at the double-coset representatives give injectivity. The
GL-refinement tensor equivalence uses ordinary indexed tensor regrouping and
actual equality transports of the block ranks. These are general induction,
topology and tensor arguments, independent of any segment conclusion.

`Classification.SupercuspidalSupport` supplies the existing cuspidal shape,
actual induced product and representation-of-datum relation. This candidate
uses their definitions and the supplied objects; it does not assume a
support-classification theorem. `Induction.BinaryProduct` supplies the actual
binary pair family, positive product, all-rank product and their proved
positive-rank isomorphism. The new private category helpers use only
`SmoothRep.mkIso`, equality elimination and this already proved general
flattening comparison.

## Recursive independence audit

The complete recursive project inventory below was checked against Library
commit `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`. It has 401 project modules,
including this new pair, and 172 direct external import roots. Every inherited
Lean/Markdown pair is present, nonempty and unchanged. There are no missing
project imports, excluded task/name pattern matches, proof holes or imports of
an unpublished candidate. The scan removes Lean comments and strings. Its
external inventory is a list of direct external roots, not a recursive Mathlib
inventory.

The wider closure inherited from general flattening includes the lower
cuspidal/Jacquet, finite-length and tensor-occurrence infrastructure. Its 18
Classification modules are explicitly listed in the project inventory; they
provide definitions, statement interfaces and general lower results. None of
the excluded segment/head/socle, full segment Jacquet or classification
conclusions is invoked by the proof route above. The extra
`FlattenedTensorOccurrences` import is not used as a mathematical input by
this construction. In particular the four derivative-named inherited modules
are only `MirabolicMinusExactnessStatement`, `MirabolicMinus`,
`MirabolicCharacter` and `ShortExactFunctorLaws`. No derivative theorem or
segment derivative formula is used. The actual proof route was checked as
well as the inventory; the import scan alone is not the independence argument.

The unchanged host exclusions of task
`8364e73f-14ec-4d14-8f2b-1555a7c1ce95` remain in force. The complete trusted
operator responses `bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920` and
`30144f6f9b59540b88b6d4c1517892d9` were read in full. This candidate uses
general induction infrastructure; it does not need the operator's conditional
permission for a newly proved support-only derivative bound. Its proof uses
none of Ze80 3.5/9.6 or their proof successors, the segment-socle part of
8e5b4563, the full host criterion in either direction, or any conclusion of
`30341ae4-65f2-4a0e-9283-763db01a409e`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`8252833d-c269-41a9-824c-5879e531b23b`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, or
`bf433f0a-921a-428c-b0c0-6475438125ac`. No pending derivative, contragredient,
product-subquotient or empty-product candidate is used.

## Remaining scope

This contribution covers positive total ranks `a,b` only. It proves no
irreducibility, finite length, support classification, product derivative
aggregation, nonlinkage survival, or linked converse. Extending this actual
comparison to zero total ranks still requires the corresponding actual
empty-product/unit comparisons. Both directions of the full
`SegmentHeadProductIrreducibility` criterion remain unproved by this pair.

## Recursive project inventory

```text
Langlands.Algebra.CommutingDimensionHelpers
Langlands.Algebra.CommutingDimensionNilpotent
Langlands.Algebra.CommutingDimensionNumerics
Langlands.Algebra.CommutingDimensionPrimary
Langlands.Algebra.CommutingDimensionRecurrence
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
Mathlib.Topology.Instances.Matrix
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.Instances.Real.Lemmas
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Separation.Profinite
```

The finite-family multiset calculation reuses the published
`Langlands.Classification.SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum`,
now shared in [MultisetOfFn](../../Algebra/MultisetOfFn.md).
