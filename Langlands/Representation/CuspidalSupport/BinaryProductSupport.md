# Actual cuspidal presentations and support addition for binary products

Author: Worker 357.

This internal construction combines two supplied actual cuspidal-product
occurrences into an actual occurrence of the binary product in the concatenated
cuspidal induction. Its grouped corollary gives the sum of two supplied
supercuspidal supports as a support of each irreducible actual subquotient of
the binary product. It uses actual representations, invariant subspaces,
quotients and isomorphisms.

The entry declaration is
`Langlands.PadicField.TopologicalData.BinaryCuspidalSupport.productOccurrenceData`.
Its return structure is `BinaryCuspidalSupport.ProductOccurrenceData`.
The corollary is
`Langlands.PadicField.TopologicalData.binaryProductConstituentSupport`.

## Parameters and supplied occurrences

All declarations have arbitrary `p : ℕ` with `[Fact p.Prime]`, an arbitrary
`F : PadicField.{uF} p`, and supplied `T : F.TopologicalData`. The topology
used on the actual general linear groups is `T.topology`. No additional
topology is chosen. The field universe `uF` and original cuspidal-carrier
universe `uV` are independent.

For natural numbers `k,l,a,b`, the constructor takes:

- Supplied families `ρ : Fin k → CuspidalDatum.{uV,uF} T` and
  `τ : Fin l → CuspidalDatum.{uV,uF} T`, with rank-sum witnesses
  `hρ : ∑ i, (ρ i).rank = a` and `hτ : ∑ i, (τ i).rank = b`.
- Supplied actual supercuspidal representatives `A i` and `C j` of the
  corresponding ranks, in `SupercuspidalRep.{uF,uV}`.
- Actual smooth complex representations `X` of `GL_a(F)` and `Y` of
  `GL_b(F)`, with carrier universe `max uF uV`.
- Supplied actual occurrences
  `SmoothRep.IsSubquotient X (T.cuspidalProductInduced ρ hρ A)` and
  `SmoothRep.IsSubquotient Y (T.cuspidalProductInduced τ hτ C)`.

Here `SmoothRep.IsSubquotient B A` has the constituent first: it supplies
an invariant subspace of `A`, an invariant kernel inside that subspace,
and an isomorphism from `B` to the resulting quotient.

The constructor does not require `X` or `Y` to be irreducible. It also
does not require representation-of-datum witnesses for `A,C`: those
witnesses are needed for the support conclusion, and are supplied there
by the two support hypotheses. No ordering, distinctness, linkage,
admissibility, finite-length or product-irreducibility assumption is added.

The original data and representatives remain in `uV`. The cuspidal
inductions, `X,Y`, binary product and chosen subquotient have carrier
universe `max uF uV`. The binary functor at that universe stays in the
same maximum universe. All natural ranks are included, with either or
both ranks zero. There is no positive-rank side condition on this pair.

## Returned actual data

Write `P(X,Y) = (T.binaryNormalizedProductFunctor a b).obj (X,Y)`.
`ProductOccurrenceData ρ τ hρ hτ A C X Y` has these fields:

| Field | Actual data retained |
| --- | --- |
| `concatenation` | `BinaryCuspidalConcatenation.AllRankData ρ τ hρ hτ A C`, containing the concatenated family, its rank sum and supplied representatives, conditional representation-of-datum witnesses, count identity, multiset identity and actual product isomorphism |
| `subspace` | An invariant subrepresentation of the cuspidal induction of `concatenation.family` |
| `kernel` | An invariant subrepresentation of the smooth representation on that subspace |
| `occurrenceIso` | An actual smooth-category isomorphism from `P(X,Y)` to the quotient by that kernel |

If `c` is the concatenation and `I` its cuspidal induction, the last
three fields have the literal types
`S : Subrepresentation I.representation`,
`K : Subrepresentation (SmoothRep.subrepresentation I S).representation`,
and `P(X,Y) ≅ SmoothRep.subquotient I S K`.
Thus the returned presentation is in one actual ambient cuspidal induction.

The inherited `c.count_eq` is `c.count = k+l`, and `c.multiset_eq` is

```text
(List.ofFn c.family : Multiset _) =
  (List.ofFn ρ : Multiset _) + (List.ofFn τ : Multiset _).
```

This identity preserves every repeated datum with its full multiplicity.
The conditional compatibility field `c.represents hA hC` uses the
original witnesses `hA,hC`; it is not an unconditional claim that arbitrary
supplied representatives represent the supplied isomorphism classes.

## Implemented constructor

First `productOccurrenceData` obtains
`c := BinaryCuspidalConcatenation.allRank ρ τ hρ hτ A C` from the
published [all-rank concatenation](AllRankBinaryCuspidalConcatenation.md).
That constructor includes the actual empty-product comparisons when a
rank is zero and uses consecutive cuspidal concatenation when both ranks
are positive.

The published
[`binaryProduct_isSubquotient`](../Induction/BinaryProductSubquotients.md)
combines the two supplied actual occurrences into

```text
SmoothRep.IsSubquotient P(X,Y)
  P(T.cuspidalProductInduced ρ hρ A,
    T.cuspidalProductInduced τ hτ C).
```

The concatenation's `c.productIso` is oriented from the flat cuspidal
induction `I` to this ambient binary product. Applying
`SmoothRep.IsSubquotient.of_iso_right` with `c.productIso.symm` therefore
moves the ambient object to `I`. Its implementation composes the
injective presentation map with the supplied ambient isomorphism.

The resulting actual subquotient relation already contains the subspace,
kernel and a nonempty type of isomorphisms. `Classical.choose` selects
the two invariant subspaces, and `Classical.choice` selects that supplied
isomorphism. The constructor packages them with `c`. It asserts no
canonical choice, naturality, or equality between this selected subspace
and a particular independently chosen presentation.

The lower product-subquotient proof first expresses each supplied
occurrence through an injective map to the factor and a surjective map
to the constituent. It applies the binary product to those maps,
takes the range of the product injection, descends the product
surjection to that range, and uses its actual kernel quotient.
For positive ranks, injectivity comes from finite tensor injectivity
over the field followed by pointwise normalized induction injectivity.
Surjectivity comes from coordinatewise lifts of pure tensors and from
smooth induction surjectivity: lift compact fixed vectors and define
the induced lift on compact open double cosets. At zero ranks, the
published actual binary tensor comparisons and ordinary tensor
injectivity/surjectivity provide the corresponding maps. These are
general algebra and induction constructions.

## Support-addition corollary

`binaryProductConstituentSupport` takes actual `X,Y` as above, an actual
smooth representation `D` of `GL_(a+b)(F)` at carrier universe
`max uF uV`, and multisets `s,t` of `CuspidalDatum.{uV,uF} T`.
Its hypotheses are exactly:

```text
T.IsSupercuspidalSupport X s
T.IsSupercuspidalSupport Y t
D.IsIrreducible
SmoothRep.IsSubquotient D P(X,Y).
```

Its conclusion is `T.IsSupercuspidalSupport D (s+t)`. The two support
hypotheses themselves include irreducibility of `X,Y`; the constructor
does not need it.

The proof unpacks each supplied support into an ordering, rank sum,
actual representatives, their representation-of-datum witnesses, and
the supplied occurrence in their cuspidal induction. It applies
`productOccurrenceData` to those occurrences. The resulting `c.family`
has multiset `s+t` by `c.multiset_eq` and the two supplied ordering
identities, total rank `a+b` by `c.rank_sum`, and representatives with
compatibility `c.represents hA hC`. The assumed irreducibility of `D`
supplies the irreducibility clause of the support definition.

For its actual occurrence in that cuspidal induction, the proof invokes
[`smoothSubquotientTransitivity`](../Filtration/SubquotientAlgebraProof.md)
on the supplied occurrence of `D` in `P(X,Y)` and the selected occurrence
of `P(X,Y)` in `I`. That published algebraic proof pulls back an invariant
subspace along the supplied surjection in an injective/surjective
presentation, restricts the surjection to that pullback, and composes
with the quotient and the actual isomorphism. It does not use the
Artinian-transfer clause proved in the same imported module.

This proves a support from supplied supports and a supplied irreducible
constituent. It does not invoke support existence or uniqueness and
does not assert that a constituent exists.

## Provenance and independence audit

This pair is an internal construction and grouped elementary corollary
from independently accepted, published actual maps and subquotient
algebra. It introduces no additional literature assertion and has an
empty source list. Its three direct imports are
`CuspidalSupport.AllRankBinaryCuspidalConcatenation`,
`Induction.BinaryProductSubquotients`, and
`Filtration.SubquotientAlgebraProof`. They remain unchanged.

The actual new proof dependencies are exactly the all-rank concatenation
constructor and its fields, the binary product-subquotient theorem,
ambient isomorphism transport, the support definition, classical
selection of an already established presentation, and the proved
transitivity of actual subquotients. Their implemented routes are
described above. The concatenation's positive branch uses general
normalized induction in stages and finite tensor regrouping through
the published `Parabolic.flattenedProductInducedEquiv`; its zero branches
use the actual empty induction, scalar tensor units, inverse carrier
lifts and exact matrix reindexing. The proof uses no segment-specific
structure or classification conclusion.

The recursive inventory below was checked at Library commit
`df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e`. It has 412 project modules
including this new pair, and 175 direct external import roots. All
inherited Lean/Markdown pairs are present, their Markdown is nonempty,
and both files are byte-identical to that Library. There are no missing
project imports, proof-hole or new-axiom matches, pending candidate
imports, or matches for the audited excluded names and task identifiers.
The lexical scan strips comments and strings. The external list records
direct external roots rather than the recursive Mathlib closure.

Relative to the published all-rank concatenation's 405-module closure,
the additional modules are this pair and the published
`Induction.BinaryProductSubquotients`, `Induction.SurjectivityProof`,
`Induction.SurjectivityStatement`, `Parabolic.InducedMapSurjectivity`,
`Tensor.ExternalMapSurjectivityProof`, and
`Tensor.ExternalMapSurjectivityStatement`. The already inherited
`SubquotientAlgebraProof` is now used for the explicit transitivity
argument above. The surjectivity bodies were inspected: they construct
actual coordinate and compact-fixed-vector lifts and do not assume a
classification statement.

The broader inherited closure contains 18 Classification modules:
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`, `FiniteLengthProof`,
`FiniteLengthStatement`, `RelativeGenericityStatement`,
`RelativeJacquetMultiplicityStatement`,
`RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
`SupercuspidalSupport`, `SupercuspidalTwist`, `Tempered`,
`TemperedInductionStatement`, and `TemperedSupportStatement`.
The used support and cuspidal-family definitions and actual subquotient
transport are in `SupercuspidalSupport`; the occurrence constructor
does not use an unproved support theorem or the inherited lower
cuspidal/Jacquet statement interfaces as hypotheses.
The only four Derivative modules are `MirabolicMinusExactnessStatement`,
`MirabolicMinus`, `MirabolicCharacter` and `ShortExactFunctorLaws`.
Neither this pair nor its used proof route invokes a derivative
conclusion. These observations supplement the lexical scan; a scan
alone would not establish semantic independence.

The trusted operator responses
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md),
and [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
were read in full. This pair needs no segment derivative permission.
It uses none of Ze80 3.5/9.6 or their proofs or proof successors,
the segment-socle part of task
`8e5b4563-0365-41c7-b134-70f2a0b36292`, the host criterion in either
direction, or the excluded conclusions of tasks
`ed48ae06-964c-4c84-9e62-978f5a953ca7`,
`b95105c6-f8bb-4641-ae53-2f49d1e7f034`,
`55ad1e10-62d8-46b7-a081-909ef0056426`,
`92aea10f-62ac-4e0b-bd4a-9a80909797c5`,
`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`,
`30341ae4-65f2-4a0e-9283-763db01a409e`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`8252833d-c269-41a9-824c-5879e531b23b`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, or
`bf433f0a-921a-428c-b0c0-6475438125ac`.

## Remaining scope

This pair supplies actual cuspidal presentations for a binary product
and support addition for its supplied irreducible subquotients. It
does not prove the support-only terminal-truncation derivative bound,
the corresponding dual initial bound, product-derivative support
aggregation or equality, nonlinkage survival or the linked converse.
Both directions of the full repeated-segment special-head product
irreducibility criterion remain unproved by this contribution.

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
Langlands.Representation.CuspidalSupport.BinaryProductSupport
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
Langlands.Representation.Induction.BinaryProductSubquotients
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
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
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
Langlands.Representation.Parabolic.InducedMapSurjectivity
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
Langlands.Representation.Tensor.ExternalMapSurjectivityProof
Langlands.Representation.Tensor.ExternalMapSurjectivityStatement
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
