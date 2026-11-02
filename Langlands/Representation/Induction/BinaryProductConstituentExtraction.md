# Actual constituent extraction in binary normalized products

Author: Worker 357.

This internal construction lifts a supplied finite filtration of either
factor to an actual filtration of its normalized binary product. It supplies
representation equivalences for every successive quotient. Applying these
constructions twice proves that a supplied irreducible subquotient of a
product of two finite-length factors occurs in the actual binary product of
irreducible subquotients of the original factors.

## Objects and scope

Fix an arbitrary prime `p`, a supplied `PadicField.{uF} p` named `F`, and
supplied `T : F.TopologicalData`. All smoothness uses `T.topology`.
Let `A` and `B` be smooth complex representations of `GL_a(F)` and `GL_b(F)`
with carriers in `Type uV`. Write

```text
P(A,B) = (T.binaryNormalizedProductFunctor a b).obj (A,B).
```

This is the published all-rank normalized binary product. Its carrier lies in
`Type (max uF uV)`. The field and original carrier universes are independent.
The natural ranks `a` and `b` are unrestricted. In particular, a rank-zero
factor retains its supplied carrier as a tensor factor. It is not replaced
by the one-dimensional trivial representation.

`Langlands.PadicField.TopologicalData.binaryProductLeftFiltrationData T A B s`
takes an actual `ObjectRepFiltration A.obj r` and returns a dependent pair
consisting of an actual `ObjectRepFiltration P(A,B).obj r` named `t` and,
for every `j : Fin r`, an actual representation equivalence

```text
(t.gradedRepresentation j).ρ ≃ P(s.smoothGradedObject j, B).representation.
```

Here and below the displayed equivalence means `Representation.Equiv`.
The analogous constructor `binaryProductRightFiltrationData` takes a
filtration `s` of `B.obj`, and its quotient comparison has target
`P(A, s.smoothGradedObject j).representation`.
The filtration length `r` is arbitrary, including zero. Neither constructor
requires finite length of the factors or simplicity of the supplied grades.
Both constructors preserve the number and order of the supplied steps.

The theorem
`Langlands.PadicField.TopologicalData.exists_irreducible_factor_subquotients_of_binaryProduct`
assumes `A.HasFiniteLength` and `B.HasFiniteLength`. For every supplied smooth
`D` of `GL_(a+b)(F)` in carrier universe `max uF uV`, it proves

```text
D.IsIrreducible →
SmoothRep.IsSubquotient D P(A,B) →
∃ E H,
  E.IsIrreducible ∧ SmoothRep.IsSubquotient E A ∧
  H.IsIrreducible ∧ SmoothRep.IsSubquotient H B ∧
  SmoothRep.IsSubquotient D P(E,H).
```

The representations `E` and `H` have the original ranks `a`, `b` and
carrier universe `uV`. Every occurrence is the existing actual smooth
subquotient relation: an isomorphism to a quotient of an invariant subspace,
equivalently its injective/surjective presentation. The theorem preserves the
supplied output `D`; it does not replace it by a formal class. Finite length
is assumed only for the original two factors. No finite-length conclusion
about the product is needed. No admissibility, segment, support, linkage or
character hypothesis is added.

## Implemented construction

The private `transportFiltrationData` takes an actual representation
equivalence from a filtered object to a smooth object, together with
equivalences from its original grades to a supplied family of smooth
objects. `LengthTwo.transport` transports the filtration. The inverse of
`ObjectRepFiltration.equivTransportGradedEquiv` identifies each transported
quotient with the original quotient; composing with its supplied comparison
gives the required result. The original and transported carrier universes
may differ.

The private `tensorCongr` is the elementary equivalence of tensor-product
representations induced by two supplied representation equivalences. Its
underlying linear equivalence is `TensorProduct.congr`, and its intertwining
identity is the tensor of the two intertwining maps.

### Positive ranks

If both ranks are positive, form `C = BlockShape.binary a b` and the actual
binary pair family furnished by `T.binaryPairFamilyFunctor`. Its slot `0`
is the left factor and its slot `1` is the right factor, with the existing
coordinate conventions.

`Parabolic.normalizedProductSlotFiltration` applies the supplied filtration
in the chosen slot. This is a filtration of the actual normalized
block-product induction. The published
`normalizedProductSlotFiltrationGradedEquivOfFamily` identifies each quotient
with the actual block product of the replacement family. In that family the
chosen slot is `s.smoothGradedObject j`; the complementary slot is the
unchanged original factor. The needed slot equivalence is reflexive because
the smooth graded object has the actual graded representation. The other
slot equivalence is reflexive after identifying the sole complementary
`Fin 2` index. Original factors are smooth, as required by this quotient
comparison.

Finally, the inverse of `T.binaryNormalizedProductPositiveIso` identifies
both the original and replacement block products with their actual binary
products. `transportFiltrationData` transports the filtration and composes
the quotient comparisons. The right-factor construction uses the same
argument at slot `1`.

The imported normalized induced quotient equivalence is unconditional here:
`Parabolic.InductionFiltration` supplies the published
`Induction.smoothInductionSurjectivity` to
`normalizedInducedSurjectivity_of_smoothInductionSurjectivity`. In
`InductionFactorMatchingProof`, the used
`nonempty_valueQuotient_equiv_induced` constructs an actual surjective
induced quotient map, identifies its kernel pointwise with the lower value
subspace, and applies the actual quotient equivalence. Its unrelated
Jordan–Hölder matching conclusion is not a hypothesis of this construction.

### Zero ranks

If `a = 0`, pull `A` back to `GL_(a+b)(F)` along the trivial group
homomorphism and pull `B` back along the canonical rank reindexing
`a+b = b`. If `b = 0` and `a ≠ 0`, use the rank reindexing `a+b = a`
for `A` and the trivial homomorphism for `B`. In either case both original
carriers are retained.

`ObjectRepFiltration.comp` pulls back the supplied filtration without
changing its underlying subspaces. `tensorRight` tensors the varying left
filtration with the fixed right factor; `tensorLeft` tensors the varying
right filtration with the fixed left factor. The respective
`tensorRightGradedEquiv` and `tensorLeftGradedEquiv`, followed by
`compGradedEquiv` and `tensorCongr`, give actual quotient comparisons for
these pulled tensor representations.

The private `leftZeroPullbackEquiv` and `rightZeroPullbackEquiv` identify
the pulled tensor representation with the corresponding published binary
product. The first comparison is the identity linear map: the factor
pulled along the trivial homomorphism acts by the identity, proved using
`map_one`. It is followed by the inverse of
`binaryLeftZeroTensorEquiv` or `binaryRightZeroTensorEquiv`. Transporting
the tensor filtration through this equivalence completes the construction.

The branch `a = 0` is taken first. Thus the case `a = b = 0` is included
without any positivity assumption or change of either carrier. Zero
filtration length also needs no separate choice of a grade.

## Implemented extraction proof

Mathlib's `isFiniteLength_iff_exists_compositionSeries` applied to `A` gives
a composition series of its group-algebra module. The published
`LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
turns it into an actual object filtration `s` with simple grades.
Apply `binaryProductLeftFiltrationData` to obtain `t`.

`t.exists_smoothGradedObject_subquotient hD hDP` selects a grade containing
the supplied irreducible subquotient `D`. This general theorem applies to
any finite object filtration; its grades need not themselves be simple.
Transport its actual occurrence through the supplied grade equivalence,
using `SmoothRep.mkIso` and `IsSubquotient.of_iso_right`. Consequently
`D` occurs in `P(s.smoothGradedObject i,B)`.

Construct a composition-series filtration `s'` for `B` in the same way.
Apply `binaryProductRightFiltrationData` with the already selected actual
left factor. A second application of actual graded extraction and
isomorphism transport gives the occurrence in
`P(s.smoothGradedObject i,s'.smoothGradedObject j)`.

Take these two actual grades as `E` and `H`. Their irreducibility is
precisely the supplied `HasSimpleFactors` assertion for the two
composition-series filtrations.
`ObjectRepFiltration.smoothGradedObject_isSubquotient` proves their actual
occurrences in their original factors. That theorem uses the actual next
invariant subspace, its injective inclusion and its surjective quotient
map. This completes the displayed conjunction.

## Provenance and dependency audit

The provenance is internal. No new assertion from external literature is
postulated or translated in this module. The construction assembles the
published actual binary product, invariant tensor filtrations, normalized
induced value filtrations, quotient equivalences and actual subquotient
extraction. The direct imports are

- `Langlands.Representation.Induction.BinaryProduct`;
- `Langlands.Representation.Parabolic.ProductInductionFiltration`;
- `Langlands.Representation.Filtration.ExactConstituentExtraction`.

The last module supplies the elementary actual occurrence of a smooth
grade. Its exact-functor image constructions and derivative exactness
interfaces are not invoked here. Tensor quotient comparisons use the
proved tensor image/quotient equivalences over the coefficient field.
Positive-rank quotient comparisons use the proved general smooth induction
surjectivity and the actual kernel calculation described above.
Composition-series conversion and arbitrary graded extraction use
group-algebra modules and invariant-subspace quotient algebra. None uses a
segment classification or derivative formula.

The recursive import inventory below was checked against published Library
`47cd8b71e79c9bb4aba6d9cc2664cb09fbff441c`. There are 133 project modules,
including this new module, and 85 directly referenced external module
roots. Every one of the 132 inherited Lean/Markdown pairs is unchanged from
that Library and has nonempty Markdown. No unresolved project import
occurs. The external list records roots imported by the project closure,
not a separate recursive traversal of Mathlib.

The classification portion of the closure consists exactly of
`ConstituentRelations`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport` and `SupercuspidalTwist`. These provide lower
definitions and actual subquotient infrastructure; no segment-head,
segment-socle or multisegment classification conclusion is used.
The derivative portion consists only of `Derivative.MirabolicMinus`,
`Derivative.MirabolicMinusExactnessStatement` and
`Derivative.MirabolicCharacter`, inherited through the unused generic
exact-functor interfaces in `ExactConstituentExtraction`. No derivative
theorem, segment derivative statement or derivative support bound is
applied by the submitted construction.

The host's independence restrictions remain in force. In particular this
closure and the inspected proof routes exclude generic unlinked-product
uniqueness (task `30341ae4-65f2-4a0e-9283-763db01a409e`), multisegment
exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head
existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage
(`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), ordered conversion
(`8252833d-c269-41a9-824c-5879e531b23b`), tempered uniqueness
(`52e97845-36bb-457d-b76f-70753334b88c`),
`SquareIntegrableLanglandsClassification`
(`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion
(`cd8ab97c-0b78-4bce-97c4-d307a28159a4`) and regular exhaustion
(`bf433f0a-921a-428c-b0c0-6475438125ac`).
Neither direction of the host's own product criterion is an input.
The additional excluded segment derivative, head, socle and full Jacquet
conclusions, including Zelevinsky 1980 §§3.5 and 9.6 and their proof
successors, are absent. The segment-socle part of task `8e5b4563-0365-41c7-b134-70f2a0b36292` is not
used.

Trusted operator decisions `bd71b9185aab5d6eafffb7891bd3a3ca` and
`0edda6122ce65ed7ac51603c37473920` retain these exclusions while
permitting independently proved general infrastructure. Decision
`30144f6f9b59540b88b6d4c1517892d9` separately permits a newly proved
support-only terminal-truncation bound. This construction makes no such
segment derivative assertion, nor any strengthening of it.
The source-name and excluded-task scan of comment- and string-stripped
Lean found no excluded conclusion or proof-hole declaration. The explicit
proof-route checks above supplement that name scan.

This is a focused prerequisite contribution. It does not prove support
aggregation, nonlinkage survival, the linked converse or the full
`SegmentHeadProductIrreducibility` criterion. The two earlier pending
modules `LeibnizConstituentExtraction` and `SegmentHeadContragredient` are
not imported or used.

## Complete project import inventory
```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicRadical
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
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.ActualGradedExtraction
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.ExactConstituentExtraction
Langlands.Representation.Filtration.ExactSmoothTransport
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.IrreducibleEmbedding
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Filtration.SmoothGradedObject
Langlands.Representation.Filtration.SubsingletonProof
Langlands.Representation.Filtration.VanishingStatement
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BinaryProductConstituentExtraction
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Parabolic.InductionFactorMatchingProof
Langlands.Representation.Parabolic.InductionFactorMatchingStatement
Langlands.Representation.Parabolic.InductionFiltration
Langlands.Representation.Parabolic.ProductInductionFiltration
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.ExternalFiltration
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteFiltration
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
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
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
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.ENat.BigOperators
Mathlib.Data.Fin.Rev
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
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
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```

## Development checks

The module and the earlier pending workspace modules compile with zero errors
and warnings in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Lake compilation and declaration inspection of the left-filtration constructor
and of the extraction theorem report independent parameters `uV` and `uF`,
with only `propext`, `Classical.choice` and `Quot.sound`. These development
checks do not establish independent semantic acceptance or publication.
