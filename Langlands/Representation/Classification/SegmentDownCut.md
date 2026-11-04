# Consecutive cuts in actual decreasing induction

Author: Worker 357.

Module `Langlands.Representation.Classification.SegmentDownCut`, namespace
`Langlands.Classification.SegmentDownCut`. This is an internal construction
from the published ordered normalized-product regrouping isomorphism, the
published binary-product object equalities, and composition of determinant-power
twists. It is defined for an arbitrary actual smooth base representation.

## Objects and resulting isomorphism

Fix `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p` and supplied
`T : F.TopologicalData`. Let `r > 0`, let `a,b > 0`, and let
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)` for `T.topology`.
Write `ν^s A` for `T.segmentFactor A s`. The construction
`segmentInducedDownCutIso a b r ha hb hr T A` returns an actual isomorphism

```text
segmentInducedDown A (a+b)
  ≅ rankCast((a*r)+(b*r) = (a+b)*r)
      (segmentInducedDown (ν^b A) a × segmentInducedDown A b).
```

Here `×` is the published `binaryNormalizedProductFunctor` at ranks `a*r` and
`b*r`; the rank equality is `(Nat.add_mul a b r).symm`. The first product
contains the original exponents `a+b-1, …, b`, and the second contains
`b-1, …, 0`. Both retain their original consecutive coordinates and order.
The two shorter decreasing inductions and the resulting objects have carriers
in `Type (max uF uV)`; the base and individual factors have carriers in
`Type uV`. The two universes are independent, and no resizing is assumed.

All inductions are the actual upper-parabolic normalized smooth inductions
with the existing half-modulus and right-translation conventions. The input
`A` need not be irreducible, supercuspidal, finite length or admissible. Only
the displayed positive ranks and cut lengths are required by the final
construction. No naturality or preferred choice of regrouping is asserted.

## General uniform cut and coordinates

`outer a b r ha hb hr` is the binary shape with sizes `a*r,b*r`, transported
to total rank `(a+b)*r`. `refinement` refines its first block into `a` blocks
of size `r` and its second into `b` such blocks. `labels` numbers the nested
blocks consecutively using `finSigmaFinEquiv` and the equality of their
number with `a+b`.

`size_eq` checks the original and nested small-block sizes. The four
`labels_zero_val`, `labels_one_val`, `labels_zero`, `labels_one` lemmas
identify the first labels with `j` and the second with `a+j`, including
the actual `Fin.castAdd` and `Fin.natAdd` indices. The private `index_val`
lemma writes each coordinate embedding as the sum of preceding block sizes
plus its internal coordinate. `coordinates` applies it to prove exactly

```text
outer.index i ((refinement i).index j x)
  = uniform.index (labels (i,j)) (cast size_eq x).
```

For the second outer block, both sides have offset `a*r+j*r`; the first
has offset `j*r`. Thus the hypotheses of the published
`Langlands.Parabolic.orderedProductRegrouping` are proved on the actual
coordinates, rather than inferred from a permutation of equal-sized blocks.

`nestedFactors` applies normalized product induction separately to the two
restricted families of an arbitrary
`X : Fin (a+b) → SmoothRep.{0,uF,uV} ℂ (GL_r(F))`, with the exact size
transports required by regrouping. `uniformNestedCutIso` selects an actual
isomorphism from the proved regrouping theorem and converts its family
expression to `nestedFactors`.

`nestedProduct_eq` identifies this outer product with the rank-transported
binary product of the two shorter uniform products. Its proof checks the
first and second outer factors using `labels_zero` and `labels_one`, then
uses the generic published
`SegmentProductSplit.binaryNormalizedProductFunctor_obj_eq` and
`SegmentProductSplit.normalizedProductInductionFunctor_rankCast_obj`.
`uniformProductCutIso` composes `uniformNestedCutIso` with the equality
isomorphism from `nestedProduct_eq`. Its conclusion preserves arbitrary
smooth factors `X`, including repeated factors, and uses the restrictions
`X (Fin.castAdd b j)` and `X (Fin.natAdd a j)`.

## Decreasing factors

`decreasingLeftIso` identifies the first restricted family for
`X = T.segmentFactorsDown A (a+b) hr` with decreasing induction of `ν^b A`.
For each `j : Fin a`, its bound proves the natural-number identity
`a+b-1-j = (a-1-j)+b`. After casting to the reals, the inverse of the published
`JuxtaposedShuffle.segmentFactorTwistIso` identifies the factor
`ν^((a-1-j)+b) A` with `ν^(a-1-j) (ν^b A)`.
The uniform product functor maps that family of actual isomorphisms.

`decreasingRightIso` similarly maps the factorwise equality obtained from
`a+b-1-(a+j) = b-1-j`. These two helper constructions require `r > 0` and
allow arbitrary natural `a,b`; the final cut construction also supplies
their positivity for the outer binary shape. Finally,
`segmentInducedDownCutIso` composes `uniformProductCutIso` with the binary
product of the two decreasing-factor isomorphisms, mapped through the
actual rank transport functor.

## Provenance and dependency audit

This unit is a direct specialization and composition of published general
constructions, with no new source assertion. In particular:

- `orderedProductRegrouping` is a proved general theorem. Its body composes
  the exact coordinate/normalization comparison, the refined-Levi tensor
  equivalence, normalized induction in stages and the proved finite-product
  induction/tensor comparison. The latter uses compact parabolic quotients.
- Only the two generic object-equality lemmas of `SegmentProductSplit` are
  used. Their proofs are equality elimination and the positive-rank definition
  of the binary product. Its other segment-datum helpers are not used.
- Only the arbitrary-smooth-object `segmentFactorTwistIso` of
  `JuxtaposedRefinementTools` is used. Its body composes `twistTwistIso` and
  equality of determinant-power characters. It proves no segment constituent
  statement. The imported `MinimalJacquetProof` supplies generic coordinate
  order lemmas to that module; its descent theorem is not used here.
- `Derivative.Iteration` supplies only `generalLinearRankCast`, which is
  equality transport and reduces to the identity after eliminating the rank
  equality. No derivative nonvanishing or segment derivative result is used.
- `Segments` supplies the actual uniform shape, twists and decreasing
  induction definitions. `LanglandsData`, `ConstituentRelations`, `Tempered`
  and the other classification interfaces in the inherited closure are
  definitions or generic transports, not classification conclusions.

The complete import traversal was checked against Library commit
`b1cc16e2270a5e556c115abf3276efff026be554`: 180 project modules including
this new module and 101 directly encountered external imports. All 179
inherited Lean/Markdown pairs match that Library byte for byte. Every
project module has paired Markdown, and no import is missing. The closure
was scanned for proof holes, new axioms, prohibited execution syntax and
the host's excluded names; there were no matches. The complete inventories
are recorded below so the audit does not rely on a private report.

This closure has no Ze80 3.5/9.6 formula or proof successor, excluded segment
socle or special-head theorem, segment Jacquet formula, full product
criterion, generic-product uniqueness, multisegment exhaustion, ordered
strong-head existence, quotient coverage, ordered conversion, tempered
uniqueness, square-integrable classification/exhaustion, or regular
exhaustion. It contains no restricted `core_mid` or length-two derivative
argument and does not use the segment-socle part of task
`8e5b4563-0365-41c7-b134-70f2a0b36292`.

The operator rulings in correspondence `bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920`,
`30144f6f9b59540b88b6d4c1517892d9`,
`ed80148e21e7523abfc048f455e98eb0`,
`2b33898bdd0a5ff1b9031be5155a06f0` and
`ca18fd5005bf5e12a3f7cade18dca865` retain all host exclusions. This
construction uses neither the support-only exception nor the reducibility
exception: its body uses only the general regrouping, twist and equality
transports described above. Importing published results adds no coauthors;
all new coordinate and specialization code in this unit is Worker 357's.

The result is an isomorphism of the full decreasing induced objects. Existence
of supplied special heads inside products of shorter heads, derivative
nonvanishing at cuts, and the linked converse of the host irreducibility
criterion remain separate obligations. This unit does not establish the
full `SegmentHeadProductIrreducibility` equivalence.

## Complete project import inventory

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
Langlands.Representation.Classification.JuxtaposedRefinementTools
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.SegmentDownCut
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

## External import frontier

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
