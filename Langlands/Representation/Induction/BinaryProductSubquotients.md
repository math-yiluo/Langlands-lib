# Actual subquotients of binary normalized products

Author: Worker 357.

This module constructs an actual subquotient presentation for the normalized
binary product from supplied presentations of both factors. The accompanying
map lemmas cover every pair of natural ranks. The provenance is internal:
these are consequences of the published tensor, normalized-induction and
actual-subquotient constructions, with no new literature assertion.

## Scope and declarations

Fix any `p : ℕ` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and any
supplied `T : F.TopologicalData`. Every topological expression uses
`T.topology`. The natural ranks `a` and `b` are arbitrary. Write

```lean
P := T.binaryNormalizedProductFunctor.{uF,uV} a b
```

and write `P(A,B)` for its object on the ordered pair. Each factor is an
actual smooth complex representation, of `GL_a(F)` or `GL_b(F)` as
appropriate, with carrier in the original universe `uV`. The field universe
`uF` is independent. All product objects, their actual invariant subspaces
and their quotients have carriers in `max uF uV`.

The four declarations are in namespace
`Langlands.PadicField.TopologicalData`:

- `binaryProductMap_injective`: for a morphism pair `f : X ⟶ Y`, if both
  actual factor intertwiners `SmoothRep.hom f.1` and `SmoothRep.hom f.2`
  are injective, the actual intertwiner `SmoothRep.hom (P.map f)` is
  injective.
- `binaryProductMap_surjective`: the same assertion for surjectivity of
  both factor maps and the product map.
- `binaryProductSubquotientData`: for factor objects `A₁,C₁,D₁` and
  `A₂,C₂,D₂`, injective maps `i₁ : C₁ ⟶ A₁`, `i₂ : C₂ ⟶ A₂`, and
  surjective maps `q₁ : C₁ ⟶ D₁`, `q₂ : C₂ ⟶ D₂`, construct an actual
  invariant subspace `S` of `P(A₁,A₂)`, an actual invariant subspace `K`
  of `SmoothRep.subrepresentation P(A₁,A₂) S`, and an actual smooth
  isomorphism
  `P(D₁,D₂) ≅ SmoothRep.subquotient P(A₁,A₂) S K`.
- `binaryProduct_isSubquotient`: if `SmoothRep.IsSubquotient D₁ A₁` and
  `SmoothRep.IsSubquotient D₂ A₂`, then
  `SmoothRep.IsSubquotient P(D₁,D₂) P(A₁,A₂)`.

The constructor returns the dependent pair of `S`, `K` and the isomorphism;
it provides actual data rather than only an existence proposition. There is
no extra compatibility requirement between the injection and surjection
of either factor span. The corollary uses the existing smooth-subquotient
relation, whose constituent is the first argument. That relation retains
an actual invariant subspace, an actual quotient of that subspace, and an
isomorphism from the supplied constituent to this quotient.

There is no finite-length, irreducibility, admissibility, finite-dimensionality,
cuspidality, support or segment hypothesis. The two factors in each pair
share `uV`, as required by the existing binary product. The results do not
assert independent universes for the two input carriers beyond that scope.

## Map proofs

For positive ranks, rewrite the binary product as the published positive
binary product. Its actual map is `T.normalizedProductInducedMap` for the
family with slots `0` and `1`. For injectivity, use
`FiniteTensor.piTensorMap_injective` on that two-slot family, and then
`T.normalizedParabolicInducedMap_injective`. The first chooses complex
linear retractions of the supplied injections and tensors them; the second
checks injectivity by evaluating the induced functions at each group
element. Neither step needs a finite-dimensional carrier.

For surjectivity in positive ranks, use the published
`Classification.normalizedProductMap_surjective F T`. It first applies
the proved general external tensor-map surjectivity theorem and then
normalized smooth-induction surjectivity. The latter obtains a common
compact open right stabilizer, lifts values in the fixed vectors of its
conjugate intersections with the closed parabolic, and assembles the
lifts over actual double cosets. This is a proved construction, with no
assumed exactness or supplied lift in the hypotheses of this module.

When `a = 0`, `T.binaryLeftZeroTensorEquiv` identifies the actual product
carrier with the tensor of the two supplied carriers. Its naturality
identifies the actual product map with `TensorProduct.map` of the two
actual factor linear maps. `TensorProduct.map_injective_of_flat_flat`
proves injection over the field `ℂ`; `TensorProduct.map_surjective`
proves surjection. For injection, apply the tensor-map injection after
the two source and target equivalences. For surjection, take a tensor
preimage and apply the inverse source equivalence; naturality and the
inverse law verify its image.

The `b = 0` branch uses `T.binaryRightZeroTensorEquiv` in exactly the
corresponding order. Taking the `a = 0` branch first includes `a = b = 0`.
Both original carrier spaces remain tensor factors, with their actual
linear maps. No arbitrary rank-zero representation is replaced by a
one-dimensional unit or discarded. The universe lift and the rank cast
of the published tensor model are handled by its actual intertwining
equivalence and naturality, rather than asserted equalities of carriers.

## Actual range, kernel and quotient construction

Let `C := P(C₁,C₂)` and `A := P(A₁,A₂)`. The constructor forms the literal
morphisms

```lean
I : C ⟶ A := P.map (i₁,i₂)
Q : C ⟶ P(D₁,D₂) := P.map (q₁,q₂)
```

The two map lemmas prove injection of `I` and surjection of `Q`. Define
`S := (SmoothRep.hom I).range`, an invariant subspace of the actual
ambient product representation. Range restriction of `I` gives an
intertwiner `j : C → S`. Its injectivity follows from that of `I`, and
its surjectivity follows from the definition of range. Equivariance of
`j` follows from equivariance of `I` and subtype extensionality.
`j.ofBijective` and `SmoothRep.mkIso` therefore give an actual isomorphism
`e : C ≅ SmoothRep.subrepresentation A S`.

The map on this range is the actual intertwiner
`q := SmoothRep.hom (e.inv ≫ Q)`. It is surjective, since the inverse
isomorphism is surjective and `Q` is surjective. Put `K := q.ker`. The
published `SmoothRep.subquotientPresentationIso S q hq` is an actual
isomorphism from `SmoothRep.subquotient A S K` onto `P(D₁,D₂)`.
Its inverse has exactly the direction returned by the constructor.
The presentation isomorphism is the quotient-by-kernel linear equivalence
with equivariance checked on representatives. The invariant subspace and
quotient are smooth by the published transfer of smoothness along actual
injections and surjections.

For `binaryProduct_isSubquotient`, apply
`SmoothRep.isSubquotient_iff_exists` separately to the two supplied
occurrences. This supplies the two injective/surjective spans, in the
original carrier universe. Apply the constructor and use its actual `S`,
`K` and isomorphism directly as the witnesses for the product occurrence.

## Provenance and dependency audit

The four project imports are the published modules
`Induction.BinaryProduct`, `Induction.Equivalences`,
`Parabolic.InducedMapSurjectivity`, and `Tensor.SmoothSubquotients`.
The two explicit external imports are `Mathlib.RingTheory.Flat.Basic`
and `Mathlib.LinearAlgebra.TensorProduct.RightExactness` at the pinned
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

This construction uses the following proved routes in those imports:

- The binary product supplies the actual positive normalized induction,
  the arbitrary rank-zero tensor models, and the naturality of their
  intertwining equivalences. It imports lower tensor, block and induction
  constructions rather than a segment product criterion.
- Injection of normalized induction is the pointwise argument in
  `Induction.Equivalences`. It assumes only injection of the inducing
  intertwiner.
- `Parabolic.InducedMapSurjectivity` uses the proved
  `FiniteTensor.externalMapSurjectivity` and
  `Induction.smoothInductionSurjectivity`. The former lifts scaled pure
  tensors and adds their preimages. The latter uses the published compact
  fixed-vector lifting and single-double-coset section constructions.
  Inflation, the common normalization character, closedness of the
  parabolic and cofinal compact open subgroups come from the supplied
  topological data and the actual block shape. This route contains no
  cuspidal, segment, head or classification conclusion.
- `Tensor.SmoothSubquotients` supplies the indexed tensor injection and
  the actual quotient presentation isomorphism. The injection proof
  tensors linear retractions. The isomorphism uses the actual quotient
  by the supplied surjection's kernel. Its inherited general external
  factor extraction is not invoked here; that argument contracts a
  complementary tensor factor after a finite-dimensional minimality
  choice and is independent of classification as well.
- `SmoothRep.isSubquotient_iff_exists` and
  `SmoothRep.hom_hom_surjective`, inherited through
  `Classification.SupercuspidalSupport`, are proved using invariant
  ranges, actual quotient maps, kernels and inverse-isomorphism identities.
  They assume no support theorem. `Category.Subquotients` uses actual
  restricted actions and actual module quotients, with the independently
  proved smoothness transfer.
- Mathlib's ordinary tensor-map injectivity uses flatness over `ℂ`, and
  its tensor-map surjectivity is ordinary algebra. No representation
  structure theorem is involved in these steps.

The complete recursive project import inventory below was reconstructed
at Library base `0ebc0efd383ff160084af3b33ab2b7806f7a1dde` after removing
Lean comments and strings. It has **175 project modules**, including this
new module, and **101 external import roots**. The external list records
roots named by these project modules, not the recursive Mathlib closure.
Every inherited Lean/Markdown pair is nonempty and byte-identical to that
published Library base. There are no unresolved project imports, proof
holes or new axioms. The forbidden-name and task scan found no matches;
the inspected actual proof routes above supply the independence argument
beyond that name scan.

The fourteen Classification modules in this closure are
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`,
`RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`,
`RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport`, `SupercuspidalTwist`, `Tempered`,
`TemperedInductionStatement`, and `TemperedSupportStatement`.
They supply lower definitions, statement interfaces and elementary
transport. Their classification-named propositions are not used as
proved inputs. In particular the used range/kernel presentation from
`SupercuspidalSupport` is elementary actual-subquotient algebra. No
representation derivative or mirabolic-theory module occurs in this
closure. Some inherited group-definition modules define the mirabolic
group; no derivative assertion is imported from them.

The host's exclusions remain in force: generic segment-product uniqueness
(task `30341ae4-65f2-4a0e-9283-763db01a409e`), multisegment exhaustion
(`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence
(`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage
(`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion
(`8252833d-c269-41a9-824c-5879e531b23b`), tempered uniqueness
(`52e97845-36bb-457d-b76f-70753334b88c`),
`SquareIntegrableLanglandsClassification` and its task
`1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable exhaustion
(`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), and regular exhaustion
(`bf433f0a-921a-428c-b0c0-6475438125ac`). None is an input, directly or
transitively, nor are their conclusions or proof successors. The present
host criterion is not an input either. The Ze80 3.5/9.6 segment derivative
formulas and their proof successors, the excluded segment/head/socle/full
Jacquet and classification conclusions, and the segment-socle part of
`8e5b4563` are not used.

Operator decisions `bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920`, and
`30144f6f9b59540b88b6d4c1517892d9` retain these exclusions while allowing
independently proved general infrastructure. This module uses that general
infrastructure only. It makes no segment derivative assertion and does
not use the support-only permission to infer a stronger result. It
imports none of the author's staged, unpublished constituent-extraction
or head-duality modules.

This unit establishes product occurrence preservation. It does not prove
support addition, product derivative support aggregation, nonlinkage
survival, the linked converse, or either direction of
`SegmentHeadProductIrreducibility`. Those remain obligations of the host.
Compilation is a development check; independent semantic acceptance and
Library publication are separate requirements.

## Project import inventory

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockUnipotent
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperUnipotent
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalField.Canonical
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
Langlands.Representation.Classification.RelativeGenericityStatement
Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
Langlands.Representation.Classification.RelativeRegularComparisonStatement
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TemperedInductionStatement
Langlands.Representation.Classification.TemperedSupportStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.CompactCoefficient.Classes
Langlands.Representation.CompactCoefficient.GroupTransport
Langlands.Representation.CuspidalSupport.AssociationLawsProof
Langlands.Representation.CuspidalSupport.AssociationLawsStatement
Langlands.Representation.CuspidalSupport.BlockMap
Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
Langlands.Representation.CuspidalSupport.GroupTransport
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.LeviAssociation
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.Central
Langlands.Representation.Exponents.ComplexTwistFamilies
Langlands.Representation.Exponents.DualJacquet
Langlands.Representation.Exponents.DualJacquetStatement
Langlands.Representation.Exponents.Jacquet
Langlands.Representation.Exponents.NilpotenceIndex
Langlands.Representation.Exponents.RealTwistFamilies
Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement
Langlands.Representation.Exponents.WeylBranchPiecesStatement
Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.MultiplicityStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BinaryProductSubquotients
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.Parabolic.InducedMapSurjectivity
Langlands.Representation.Parabolic.OppositeRefinementDefinitions
Langlands.Representation.Parabolic.OppositeRefinementFunctors
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.GroupEquivalence
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.ExternalMapSurjectivityProof
Langlands.Representation.Tensor.ExternalMapSurjectivityStatement
Langlands.Representation.Tensor.ExternalSubquotient
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Tensor.SmoothSubquotients
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
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
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

## External import roots

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Analysis.Complex.Basic
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
Mathlib.Data.ENat.Basic
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.LinearAlgebra.AffineSpace.AffineMap
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.Finiteness
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.Length
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.Instances.Real.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
