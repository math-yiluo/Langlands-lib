# Positive binary products on the explicit two-block shape

This internal adapter constructs
`Langlands.PadicField.TopologicalData.binaryNormalizedProductTwoBlockIso`.
For every prime `p`, actual `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, positive ranks `a,b`, and smooth complex
representations `A` and `B` of `GL_a(F)` and `GL_b(F)`, its type is

```lean
(T.binaryNormalizedProductFunctor a b).obj (A,B) ≅
  (T.normalizedProductInductionFunctor (Shahidi.twoBlocks a b ha hb)).obj
    (Fin.cases A (Fin.cases B finZeroElim))
```

The two factor carriers share the arbitrary universe `uV`; the field universe
`uF` is independent. Both displayed induced carriers are in
`Type (max uF uV)`. The supplied topology is retained throughout. The only
rank hypotheses are `ha : 0 < a` and `hb : 0 < b`. There is no irreducibility,
admissibility, finite-length, finite-dimensionality, segment or derivative
premise. This definition returns an actual categorical isomorphism of smooth
representations, with an equivariant map and inverse, rather than just equality
of classes or an existence proposition. No naturality statement is exported.

The first coordinate remains `A` and the second remains `B`. Both sides use
the upper standard parabolic and the same positive half-modulus character,
after equality transport of the shape. There is no permutation, duality,
determinant twist, change of field or resizing of the original factor carriers.
The isomorphism identifies two presentations of the same normalized induction.
It proves no irreducibility criterion or derivative formula and does not
complete `Langlands.Classification.SegmentHeadProductIrreducibility`.

## Implemented construction

The two direct imports are `Induction.BinaryProduct` and `Shahidi.TwoBlocks`.
The former defines the all-rank binary product by cases: when both ranks are
positive it is `binaryPositiveProductFunctor`, itself the composition of
`binaryPairFamilyFunctor` with normalized product induction on
`GeneralLinear.BlockShape.binary a b ha hb`. The latter defines
`Shahidi.twoBlocks a b ha hb` with sizes `![a,b]`.

The private helper `binaryShape_eq_twoBlocks` unfolds these two shapes. Both
have length two and their size functions agree at each of the two indices;
function extensionality, `fin_cases`, and proof irrelevance establish equality
of the structures. This is an equality of the actual indexed block shapes,
not a comparison based only on their total ranks.

The private helper `productObject_congr` takes equality of two block shapes
and heterogeneous equality of their dependent families of smooth
representations. Eliminating these equalities makes the two normalized
product objects definitionally equal. It introduces no additional theorem
about induction or representations.

The main definition rewrites the published
`binaryNormalizedProductFunctor_of_pos ha hb`. After exposing the positive
product, its object is normalized product induction of the ordered family
provided by `binaryPairFamilyFunctor`. The shape equality and
`Function.hfunext` compare this family with
`Fin.cases A (Fin.cases B finZeroElim)`; each of the two indices reduces to
reflexivity. `productObject_congr` yields equality of the smooth objects, and
`eqToIso` turns this equality into the stated actual isomorphism. The source
and target actions, smoothness witnesses, and normalization therefore agree
by equality transport. The proof invokes no analytic integral, irreducibility
or exactness theorem.

## Internal provenance and existing work

This is elementary transport between two published constructions. It asserts
no new transcription from literature, so its provenance is internal and its
source list is empty. The mathematical meaning of its inputs is supplied by
their published Lean/Markdown pairs; no separate source theorem about
segments is used.

The published module
`Classification.TwoSupercuspidalBinaryProductBridge` contains related
`binary_eq_twoBlocks`, `normalizedProductInductionFunctor_obj_congr`, and
`binaryNormalizedProductFunctor_obj_eq_twoBlocks` declarations. They were
read for comparison. That module imports
`TwoSupercuspidalProductStructureStatement`, which is outside this host's
permitted dependency boundary. The present definition separately implements
the elementary shape/family equality argument in the generic induction layer
and packages an actual isomorphism. It imports neither that bridge nor its
product-structure statements. The published
`binaryNormalizedProductPositiveIso` already compares the all-rank binary
functor with its positive branch; it does not express the dependent family on
`Shahidi.twoBlocks`. This focused adapter supplies that remaining comparison.

## Dependency and proof audit

The complete project import closure was traversed against published Library
`475b3be9b8c1a751adde2d3a86b8cbb5f831142a`. It contains 39 project modules,
including this one, and 49 distinct external frontier imports. Every one of
the 38 inherited Lean/Markdown pairs agrees byte for byte with that Library.
There are no missing pairs, unproved placeholders or custom axioms in the
project closure. The complete module inventories are below.

The used proof bodies are the positive-branch case reduction of
`binaryNormalizedProductFunctor_of_pos`, the definitions of
`binaryPositiveProductFunctor`, `binaryPairFamilyFunctor`,
`normalizedProductInductionFunctor`, `BlockShape.binary` and
`Shahidi.twoBlocks`, together with ordinary equality elimination, function
extensionality and categorical equality transport. The normalized product
uses the existing indexed block tensor and the existing positive
half-modulus. No formula for that modulus is needed by this adapter.

There are no representation derivative, representation mirabolic or
classification modules in this closure. The group-level mirabolic modules
supply general matrix constructions imported by `BinaryProduct`; no derivative
result is extracted from them. `Jacquet.PositiveCharacter` supplies elementary
positive characters for normalized induction, not a segment Jacquet formula.
Neither the host criterion, its parent uniqueness theorem nor an excluded
segment/head/socle or classification proof is used. In particular,
`SegmentHeadSupportStep`, `SegmentHeadJacquetReduction`, the support-truncation
proof and its restricted `core_mid` intermediate, Zelevinsky 1980 3.5/9.6 and
their proof successors, `TwoSupercuspidalProductStructureProof`, and
`UniverseLiftPadic` are absent. The permission confined to the length-two
support proof is not invoked. No pending candidate is imported.

The host's operator rulings are preserved: the general derivative permission
in responses `bd71b9185aab5d6eafffb7891bd3a3ca` and
`0edda6122ce65ed7ac51603c37473920`, the exact support-only boundary in
`30144f6f9b59540b88b6d4c1517892d9`, and the restricted support-proof exceptions
in `ed80148e21e7523abfc048f455e98eb0`,
`2b33898bdd0a5ff1b9031be5155a06f0`, and
`ca18fd5005bf5e12a3f7cade18dca865`. This adapter needs none of those exceptions;
its construction is general equality transport within normalized induction.

## Complete project module inventory

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.UpperUnipotent
Langlands.Group.LeftQuotient
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BinaryTwoBlockIso
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.Definitions
Langlands.Topology.CompactNormCharacter
```

## Complete external frontier inventory

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
