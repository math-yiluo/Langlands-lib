# The first factor and ordered tail as a literal binary product

Author: Worker 357.

This internal adapter composes the published first/tail regrouping with the
published all-rank binary product functor and equality transport of the ambient
rank. It supplies an actual categorical isomorphism, retaining the original
first factor. It does not prove a derivative formula or an irreducibility
criterion.

For arbitrary `p : ℕ` with `Fact p.Prime`, a supplied
`F : PadicField.{uF} p` and `T : F.TopologicalData`, let
`B : GeneralLinear.BlockShape n` and `h : B.length = k + 2`.
The factor family has carriers in `Type (max uF uV)`, where `uF` and `uV`
remain independent. The tail is the actual normalized product on
`B.tailShape h` of `σ (B.tailIndex h j)`, in the original order.

`normalizedProductInductionRankTransportIso T hr C τ` compares equality
transport of an induced object along `hr : m = n` with product induction on
`C.rankCast hr`. Its proof eliminates only that equality and returns the
identity isomorphism.

`headTailBinaryProductIso T B h σ` maps the product on `B` to
`Derivative.generalLinearRankCast T (B.headRank_add_tailRank h)` applied
to the literal `T.binaryNormalizedProductFunctor` of the original head
`σ (B.headIndex h)` and the actual tail product. The two binary ranks are
positive by the published head/tail geometry.

The proof first applies `headTailProductInductionIso`. At the first outer
slot, the inverse of `SmoothRep.universeLiftEquiv` identifies the lifted
head with the original head; at the second slot the map is the identity.
Both objects are in the same category because the input universe already
contains `uF`. The normalized outer product maps this family isomorphism.
Next, the inverse rank-transport comparison rewrites the resulting
two-block product as equality transport of the positive binary product.
Finally, equality transport maps `binaryNormalizedProductPositiveIso`,
and its inverse gives the literal all-rank binary functor in the target.

All carriers stay in `Type (max uF uV)` throughout. No resizing or replacement
of the original head object occurs in the target. The ambient rank equality
has direction `headRank + tailRank = n`. The underlying upper-parabolic
normalization and right-translation actions are those of the imported
actual product functors. No evaluation formula for the chosen regrouping
isomorphism, naturality in the shape, empty-tail case, support existence,
finite length, admissibility, irreducibility or segment result is claimed.

The provenance is internal composition of published category, carrier-lift,
ordered-regrouping, binary-product and rank-equality constructions.

## Published inputs and proof route

The source list is empty: this pair translates no additional external
theorem. Its three direct imports have the following roles.

| Module after `Langlands.Representation.` | Role |
| --- | --- |
| `Parabolic.HeadTailProductInduction` | The actual first/tail regrouping isomorphism and ordered head/tail factors |
| `Induction.BinaryProduct` | The literal binary functor, its positive-rank comparison and the two-slot factor family |
| `Derivative.Iteration` | The equality-transport functor `generalLinearRankCast` |

The existing first/tail isomorphism is reused. It specializes the proved
general `Langlands.Parabolic.orderedProductRegrouping` to the published
`HeadTailBlocks` coordinates. That theorem composes the actual normalized
coordinate comparison, the finite external-tensor refinement equivalence,
normalized induction in stages, and the tensor/induction comparison.
The singleton head is identified with its carrier lift by the published
single-block construction. Each of these is a general construction for
supplied smooth representations, with no segment hypothesis.

The `ThreeBlock` and heterogeneous modules inherited through the first
import were also examined. Their carrier and geometry maps use consecutive
coordinates, tensor reassociation, `ULift.up` and `ULift.down`. Their
associativity interfaces retain the stated general regrouping premises.
The first/tail construction uses the closed ordered-regrouping theorem
above; it does not assume one of those interfaces as an unproved theorem.
Occurrences of the `Shahidi` namespace there name concrete pair shapes
and actions. No analytic local-coefficient identity supplies an input.

The new helper `normalizedProductInductionRankTransportIso` eliminates
`h : m = n`; the imported `generalLinearRankCast` is `Eq.rec` of the
identity functor. Thus its use here invokes no derivative comparison,
exactness, finite-length or segment theorem. At positive ranks the
imported binary functor comparison is the isomorphism induced by its
proved equality with product induction on `BlockShape.binary`.
The new entry only maps and composes these actual isomorphisms.

Searching the current Library found the reused
`headTailProductInductionIso`, but no declaration named
`headTailBinaryProductIso` or
`normalizedProductInductionRankTransportIso`. The existing comparison
ends in an outer two-block family with a lifted head. This adapter
provides the literal binary functor on the original head, the original
ordered tail product, and the exact ambient rank transport needed by
binary consumers.

## Host independence audit

The recursive inventory at Library
`96e2bf23b0d79b978b965af2fce2d0d47ad24661` has 172 project modules,
including this entry, and 98 directly named external import roots.
All 171 inherited Lean/Markdown pairs are present, have nonempty
Markdown and are byte-identical to the published Library. There are
no missing project imports or pending imported candidates.
The inventory below lists project modules recursively and external
roots directly; it does not claim a separate recursive traversal
of Mathlib.

Every inherited pair has the same fingerprints as a previously read
and audited input pair. The general induction, tensor, rank-transport
and derivative-construction closure was covered by the binary derivative
support audit. The additional first/tail closure was read in full as
Lean/Markdown pairs: the head/tail and adjacent-merge geometry, carrier
lift and block equivalence, heterogeneous constructions and pairs,
ordered regrouping statement, equivalence and proof, factor equivalences,
and the five inherited three-block carrier, geometry, universe,
associativity-interface and assembly modules. The current inventory
comparison leaves only this new entry outside that union.
This is a comparison of source fingerprints and proof routes; it uses
no pending aggregation candidate as a mathematical premise.

Exactly four `Classification` modules occur:
`Supercuspidal`, `SupercuspidalTwist`,
`SupercuspidalContragredientAux`, and
`SupercuspidalContragredientStatement`.
The only modules under `Representation.Derivative` are `Iteration`,
`MirabolicMinus` and `MirabolicCharacter`, all general functor
constructions. No segment or classification conclusion is invoked
by the implemented isomorphisms.

The trusted operator responses
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md),
and [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
were read in full. They retain the host exclusions while permitting
independently proved general infrastructure and, separately, a new
exactly support-only terminal-truncation bound. This adapter proves
no segment support bound and uses none as an input.

| Excluded result or boundary | Check on the closure and implemented route |
| --- | --- |
| Ze80 §§3.5/9.6, their formulas, proofs and proof successors | No segment derivative module is imported or invoked. The only rank-transport dependency is equality elimination. |
| Full segment/head/socle Jacquet formulas and exponent norm formula, including tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | None supplies a dependency. General induction and coordinate constructions do not apply these conclusions. |
| Host criterion `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` in either direction and socle product criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Neither conclusion, a proof successor nor a downstream criterion consumer is imported or used. |
| Parent uniqueness `30341ae4-65f2-4a0e-9283-763db01a409e` | No uniqueness or comparison of different segment products is used. |
| Multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, ordered conversion `8252833d-c269-41a9-824c-5879e531b23b` | None supplies an input. The factor family here is supplied and the refinement is geometric. |
| Tempered uniqueness `52e97845-36bb-457d-b76f-70753334b88c`, `SquareIntegrableLanglandsClassification` and task `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac` | These conclusions and proof routes are absent. |
| Segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292`, linked-pair structure, adjacent commutation and two-supercuspidal product criteria | None is used by the actual general induction isomorphisms. |
| Whittaker irreducible/Levi/supercuspidal coinvariant finiteness and dependent mirabolic finite length | These conclusions are absent; this construction needs no finite-length assertion. |
| Original carrier parameters, order and repeated factors | `uF,uV` remain independent; carriers stay at `max uF uV`, the target uses the original head and actual ordered tail, and there is no distinctness premise or removal of repeated factors. |
| Pending results and run controls | All imported inputs are published. The pending support aggregation and support-only proof are not used; no paused proof owner is needed for this unit. |

A recursive lexical scan after removing nested comments and strings
found no audited excluded-name or task-identifier matches, proof holes,
new axioms or prohibited execution syntax. The proof-route examination
above supplements the scan; a name scan alone would not establish
independence.

## Validation and remaining scope

Recovery draft check `81067f22-dcde-49dd-9b38-4a3e31ab78df` compiled
this module with zero errors and warnings in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Exact entry inspection and Lake build
`ab429bf5-021e-4038-8962-e289349eaaed` also passed with zero errors
and warnings. The entry is a definition with independent level
parameters `uF,uV` and only `propext`, `Classical.choice` and
`Quot.sound`. Final ordinary-module Lake build and exact entry inspection
`50df741f-c703-4b50-809a-56fad3c9fa80` reproduced that clean result,
with the same source and type fingerprints. No Lean edit followed it.
These development checks establish no independent semantic acceptance
or publication.

This focused comparison supplies one adapter for finite-product
iteration. It does not itself iterate derivatives or support witnesses,
prove a terminal-truncation support bound, identify a derivative
with a truncated head, prove derivative irreducibility or multiplicity,
or prove either direction of the host irreducibility criterion.
Those obligations remain open.

## Complete project import inventory

### Langlands.Group (29)

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
```

### Langlands.HarmonicAnalysis (1)

```text
Langlands.HarmonicAnalysis.Basic
```

### Langlands.LocalFactor (1)

```text
Langlands.LocalFactor.Euler.Definitions
```

### Langlands.LocalField (7)

```text
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
```

### Langlands.Representation.Category (4)

```text
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Category.UniverseLift
```

### Langlands.Representation.Classification (4)

```text
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalTwist
```

### Langlands.Representation.Compact (2)

```text
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
```

### Langlands.Representation.Conductor (1)

```text
Langlands.Representation.Conductor.Congruence
```

### Langlands.Representation.CuspidalSupport (6)

```text
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
```

### Langlands.Representation.Derivative (3)

```text
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
```

### Langlands.Representation.Dual (1)

```text
Langlands.Representation.Dual.Definitions
```

### Langlands.Representation.Exponents (1)

```text
Langlands.Representation.Exponents.ParabolicPair
```

### Langlands.Representation.Filtration (2)

```text
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.ObjectDefinitions
```

### Langlands.Representation.Geometric (8)

```text
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
```

### Langlands.Representation.Induction (17)

```text
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
Langlands.Representation.Induction.HeadTailBinaryProduct
Langlands.Representation.Induction.HeterogeneousConstruction
Langlands.Representation.Induction.HeterogeneousPairs
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.StructuralStatement
```

### Langlands.Representation.Jacquet (7)

```text
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
```

### Langlands.Representation.MatrixCoefficient (3)

```text
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
```

### Langlands.Representation.Parabolic (25)

```text
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
```

### Langlands.Representation.Shahidi (3)

```text
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.TwoBlocks
```

### Langlands.Representation.Smooth (20)

```text
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
```

### Langlands.Representation.Tensor (6)

```text
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
```

### Langlands.Representation.Twist (13)

```text
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
```

### Langlands.Representation.Unitary (1)

```text
Langlands.Representation.Unitary.Basic
```

### Langlands.Representation.Whittaker (3)

```text
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.Iwasawa
```

### Langlands.Topology (4)

```text
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```

## Direct external import roots

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
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
