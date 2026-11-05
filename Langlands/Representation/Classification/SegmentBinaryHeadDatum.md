# Actual data for a supplied binary special-head product

Author: Worker 357.

This derived construction packages two supplied actual special heads as
`SegmentProductDatum`, preserving the blocks, their order, their cuspidal
multiplicities, and an actual equivalence with their binary normalized product.
It uses the published shape-comparison and binary-product interfaces.

## Parameters and exact result

Fix arbitrary `p : ℕ`, `[Fact p.Prime]`, `F : PadicField.{uF} p`, and supplied
`T : F.TopologicalData`. The universes `uF` and `uV` are independent.
For `Δ Γ : T.Segment.{uV,uF}`, supply actual smooth complex representations

```lean
π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)
τ : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)
```

with `T.topology` installed, and proofs `hπ : T.IsSegmentHead Δ π` and
`hτ : T.IsSegmentHead Γ τ`. The head relation is the existing strong
irreducible quotient relation for the increasing normalized induction of
the segment's cuspidal members. The constructor never replaces either supplied
representation by a newly chosen head, and does not substitute a segment
socle for a head.

In `Langlands.Classification`, the structure `SegmentBinaryHeadDatum T Δ Γ π τ`
has the following fields.

| Field | Meaning |
| --- | --- |
| `datum` | Actual `T.SegmentProductDatum.{uV,uF} (Δ.degree + Γ.degree)`. |
| `heads` | Every block of `datum` satisfies the existing special-head relation. |
| `segments` | Its exact ordered list is `List.ofFn datum.segments = [Δ,Γ]`. |
| `content` | `datum.multisegment.cuspidalContent = Δ.cuspidalContent + Γ.cuspidalContent`. |
| `equivalence` | Actual equivariant complex-linear equivalence from `datum.induced.representation` to `((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ)).representation`. |

The definition `segmentBinaryHeadDatum T Δ Γ π τ hπ hτ` returns this data.
Its premise list has no linkage, precedence, distinctness, twist-freeness,
ambient-product irreducibility, or additive-character assumption. The same
segment may occupy both positions, and equal cuspidal members contribute
repeatedly to `content`. Both degrees are positive by the existing segment
definition. The actual block and induced carriers are in `Type (max uF uV)`;
the cuspidal bases remain in the unsaturated `Type uV`.

The public structure records the ordered segment list and the equivalence to
the supplied binary product. It does not expose additional block-equality
fields. The implementation uses exactly `π` and `τ` in its two block entries.

## Implemented construction

The local datum has length two and segment family
`Fin.cons Δ (Fin.cons Γ Fin.elim0)`. Its block family uses `Fin.cases`
to put `π` in position zero and `τ` in position one; the remaining index type
is `Fin 0`. The sum of the degrees reduces by `Fin.sum_univ_succ`.
Case analysis on the two indices proves `HasSegmentHeads` using `hπ` and
`hτ`. `List.ofFn_cons` and `List.ofFn_zero` recover the exact segment list.

For the content field, the definition of `datum.multisegment` is the multiset
underlying this list. Rewriting the list to `[Δ,Γ]` and unfolding
`Multisegment.cuspidalContent` gives the displayed sum by multiset map and sum
identities. This proof counts the full indexed content of each occurrence;
it does not pass to a set.

Let `B := BlockShape.binary Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos`.
Its length and its two sizes are the local datum's length and degrees.
The size identity `hs` is proved by the two finite-index cases. The factor
family on `B` is

```lean
X i := (hs i).symm ▸ d.blocks (Fin.cast rfl i)
```

so the published `d.inducedEquivOfShape B rfl hs` gives an actual equivalence
from the datum product to the normalized block product of `X`. This published
helper proves equality of the ordered shapes using `BlockShape.ext_of_size`
and reduces to the identity equivalence. It requires no commutation or
classification result.

The published `SegmentProductSplit.binaryNormalizedProductFunctor_obj_eq`
identifies the supplied binary product with that same block product, since
`X 0 = π` and `X 1 = τ` by reflexivity. Its proof unfolds the positive-rank
branch of the binary functor and proves equality of the two-entry factor
families by finite-index cases. The constructor reverses this object equality,
forms `eqToIso`, converts it with `SmoothRep.equivOfIso`, and composes it with
the preceding shape equivalence. This explains the direction of the stored
equivalence from `datum.induced` to the supplied binary product.

The constructor has the finite local elaboration budget
`maxHeartbeats 800000`. This changes no mathematical premise. Exact declaration
inspection reports a definition with independent level parameters `uF,uV`
and only `propext`, `Classical.choice`, and `Quot.sound`.

## Provenance, reuse, and scope

This is derived finite data assembly from published definitions and adapters,
with no new assertion taken from literature. The existing `SegmentProductDatum`,
`HasSegmentHeads`, `IsSegmentHead`, `cuspidalContent`, and positive binary
normalized product supply all conventions. The two published adapter bodies
used here were inspected. A current-Library declaration search found no
existing `SegmentBinaryHeadDatum` or `segmentBinaryHeadDatum`.

The related `SegmentProductDatum.inducedEquivOfShape` is reused rather
than repeated. It starts with an existing datum and compares ordered shapes;
it does not construct the two-head datum or store its list and content.
`SegmentProductSplit.binaryNormalizedProductFunctor_obj_eq` is likewise
reused. Its result is object equality for a supplied binary factor family;
the present constructor assembles that family and the required head and
content data. These existing interfaces are not replaced.

The full `SegmentHeadProductIrreducibility` criterion remains a separate
obligation. This constructor establishes no irreducibility of the binary
product, no linked-pair contradiction, no original/replacement comparison,
and no assertion about a derivative. It is an actual-data prerequisite under
the host task, rather than a proof of either direction of the final criterion.

## Independence audit

The audit is against Library commit
`9caf47cacd8f25d9a56aa0737b4256267bf62d16`.
The three direct project imports have these roles.

| Import | Used declarations and role |
| --- | --- |
| `Classification.SegmentProductRefinement` | `SegmentProductDatum.inducedEquivOfShape`: actual product equivalence on an equal ordered shape, proved from shape extensionality. |
| `Classification.SegmentProductSplit` | `binaryNormalizedProductFunctor_obj_eq`: the positive binary functor is the normalized block product of its two supplied factors. |
| `Classification.SegmentCuspidalContent` | The indexed multiset definitions and elementary map/sum identities for the content field. |

The recursive inventory below contains 189 project modules, including this
new pair, and 107 distinct external frontier imports. All 188 inherited
Lean/Markdown pairs are byte-identical to that Library. No project import or
paired Markdown is missing. The comment/string-stripped scan finds no proof
holes, new axioms, prohibited execution syntax, or excluded-conclusion names.
The scan is an absence check; the semantic independence of the used code
also follows from the shape identity and finite-family proofs described above.

The graph includes `Derivative.Iteration`, `Derivative.MirabolicMinus`, and
`Derivative.MirabolicCharacter` through the published product-split module.
These provide general functor definitions; this construction invokes no
derivative assertion or exactness theorem. Imported parabolic regrouping and
adjacent segment-replacement modules are also unused by its proof body.
Their presence supplies no additional hypothesis to this constructor.

The trusted operator decisions read in full for this host are correspondence
files `bd71b9185aab5d6eafffb7891bd3a3ca.md`,
`0edda6122ce65ed7ac51603c37473920.md`,
`30144f6f9b59540b88b6d4c1517892d9.md`,
`ed80148e21e7523abfc048f455e98eb0.md`,
`2b33898bdd0a5ff1b9031be5155a06f0.md`, and
`ca18fd5005bf5e12a3f7cade18dca865.md`.
They retain the host's independence exclusions while permitting the specified
proved general foundations and final support-only bound. The present unit
needs none of the derivative, reducibility, or support-bound permissions.

Its closure excludes Ze80 3.5/9.6 and their proof successors; the excluded
segment/head/socle/full-Jacquet and classification conclusions; the
segment-socle component of task `8e5b4563-0365-41c7-b134-70f2a0b36292`;
`SegmentHeadSupportStep`, `SegmentHeadJacquetReduction`,
`TwoSupercuspidalProductStructureProof`, and `UniverseLiftPadic`.
It imports no pending `SegmentHeadProductComparison` or
`SegmentHeadReplacementDatum`.
It also excludes the parent generic-product uniqueness and all other
independence tasks listed by the host:
`30341ae4-65f2-4a0e-9283-763db01a409e`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`8252833d-c269-41a9-824c-5879e531b23b`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`, and
`bf433f0a-921a-428c-b0c0-6475438125ac`.
Imported classification statement modules supply only their existing predicates
and data; none is used as a proved classification input.


## Complete recursive project import inventory

```text
Langlands.Combinatorics.RelationInversions
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
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.SegmentBinaryHeadDatum
Langlands.Representation.Classification.SegmentCuspidalContent
Langlands.Representation.Classification.SegmentIntegralCoordinates
Langlands.Representation.Classification.SegmentIntervalLinkage
Langlands.Representation.Classification.SegmentProductAdjacentReplacement
Langlands.Representation.Classification.SegmentProductRefinement
Langlands.Representation.Classification.SegmentProductReplacement
Langlands.Representation.Classification.SegmentProductSplit
Langlands.Representation.Classification.SegmentReplacementInversions
Langlands.Representation.Classification.SegmentUnionIntersection
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

## Complete external frontier import inventory

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Group.List.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Int.Interval
Mathlib.Data.List.FinRange
Mathlib.Data.List.Pairwise
Mathlib.Data.List.TakeDrop
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.Hom.Set
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
