# Determinant twists of supercuspidal supports

Author: Worker 357.

This internal derived helper transports the existing support relation along a
real determinant-power twist. It uses the actual cuspidal representatives,
injection, quotient map and published normalized product-twist equivalence.
It makes no derivative assertion.

`SmoothRep.IsSubquotient.twist` twists the intermediate object and both maps in
the injection-and-surjection characterization of a subquotient. The underlying
linear maps are unchanged, so their injectivity and surjectivity are retained.

`normalizedProductDeterminantTwistIso` is the selected construction. It returns
an actual smooth-category isomorphism by bundling the published
`CuspidalProductContragredient.nonempty_twist_productEquiv` with
`SmoothRep.mkIso`, after classical selection of the published nonempty
equivalence. This selection is not asserted to be canonical. The published `normalizedProductInductionFunctor_obj`
identifies both bundled actions. The constituent transport below uses this
constructed isomorphism directly. A local finite heartbeat limit of 2,000,000
allows Lean to compare the expanded induced carrier and module instances.
This changes elaboration resources only.

`IsCuspidalConstituent.twist` twists the supplied supercuspidal representatives
and the actual constituent. Their ranks are unchanged. The representative
classes are the prescribed twisted cuspidal classes by definition.
Irreducibility is preserved by the published twist theorem. The published
`CuspidalProductContragredient.nonempty_twist_productEquiv` identifies the twist
of the ambient product with the product of the twisted representatives, and
the twisted occurrence is transported along this actual isomorphism.

`IsSupercuspidalSupport.twist` applies that construction to an ordering of the
given multiset. Mapping the ordered list produces exactly its multiset image.
Thus multiplicities are retained. The result covers arbitrary real exponents,
rank zero, arbitrary prime fields with their supplied topological data, and
independent field and base carrier universes. The constituent carrier remains
in `Type (max uF uV)` while support data remain in the original base universe.

The provenance is the definition of supercuspidal support as an irreducible
cuspidal-product occurrence, together with the already published actual
normalized product-twist equivalence. The proof is a direct composition of
these constructions, with no additional literature assertion or hypothesis.
It neither assumes nor proves any segment derivative formula or product
irreducibility criterion.

## Dependency and proof-route audit

At Library base `e01d121751dd80ba2ce2d21544b43f6e8df18007`, the recursive
inventory contains 242 project modules including this entry and 123 directly
named external import roots. There is one direct import,
`Langlands.Representation.Classification.CuspidalProductContragredient`.
All 241 inherited Lean/Markdown pairs are byte-identical to the current
Library and to the corresponding pairs in the previously accepted
`SegmentHeadProductDualInitialSupport` dependency audit. No project import or
paired Markdown is missing. The complete inventories are below; the external
list records direct roots rather than a separate recursive Mathlib audit.

The implemented proof uses the general twist functor on actual objects and
maps, the injection-and-surjection characterization of a subquotient,
the actual normalized block-product twist equivalence, preservation of
supercuspidality and irreducibility under character twists, and the defining
ordered witness for a support multiset. It uses neither uniqueness nor
existence of arbitrary supercuspidal supports.

The inherited cuspidal-product module also provides general contragredient
and induction-duality results, which are not used by this proof. Its
classification imports consist of cuspidal data, support and constituent
definitions, elementary twist and dual transport, the independently proved
supercuspidal contragredient theorem, and the general cuspidal Jacquet
multiplicity Prop interface. No derivative or mirabolic module is in this
closure. No published Prop interface is treated as a proved input.

The host's trusted operator correspondence
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md),
[30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md),
[ed80148e21e7523abfc048f455e98eb0](/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md),
[2b33898bdd0a5ff1b9031be5155a06f0](/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md),
and [ca18fd5005bf5e12a3f7cade18dca865](/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md)
was read in full. The narrow exceptions for the individual support proof's
length-two base do not enter this unit: it imports no adjacent-reducibility,
terminal-support, `core_mid` or `core` result.

The inherited closure and the new proof are independent of the host criterion
in either direction; parent `GenericSegmentProductUniqueness`; multisegment
exhaustion; ordered strong-head existence; quotient coverage; ordered
conversion; tempered uniqueness; square-integrable classification and
exhaustion; regular exhaustion; Ze80 3.5/9.6 and their proof successors;
excluded segment, head, socle and full Jacquet conclusions; and the
segment-socle part of task `8e5b4563`. The broad lexical scan of the full
Lean closure has no hit for the host exclusion inventory. The route and
fingerprint checks above supplement this lexical check.

## Validation

The complete native module and selected construction compiled in the project's
authorized Lean service with zero errors and warnings. Declaration inspection
identifies the selected construction as a definition, with independent `uF`
and `uV` and only the standard `propext`, `Classical.choice` and `Quot.sound`
axioms. Independent semantic review and publication
remain separate requirements.

## Complete project import inventory

```text
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockContractionProof
Langlands.Group.GL.BlockContractionStatement
Langlands.Group.GL.BlockIwahoriBasis
Langlands.Group.GL.BlockIwahoriBasisStatement
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockModulusHaarProof
Langlands.Group.GL.BlockModulusHaarStatement
Langlands.Group.GL.BlockUnipotentCoordinates
Langlands.Group.GL.BlockUnipotentHaarProof
Langlands.Group.GL.BlockUnipotentHaarStatement
Langlands.Group.GL.Blocks
Langlands.Group.GL.CartanProof
Langlands.Group.GL.CartanStatement
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.IntegralSubgroup
Langlands.Group.GL.InverseTransposeIwahoriProof
Langlands.Group.GL.InverseTransposeIwahoriStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OneBlockShape
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.ParabolicModularCharacter
Langlands.Group.GL.PrincipalBlockFactorizationProof
Langlands.Group.GL.PrincipalBlockFactorizationStatement
Langlands.Group.GL.RankMaps
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UpperUnipotent
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.TriangularTranslationProof
Langlands.HarmonicAnalysis.TriangularTranslationStatement
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Contragredient
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.CuspidalProductContragredient
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredient
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientProof
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalSupportTwist
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Conductor.Definitions
Langlands.Representation.Conductor.PrincipalCongruence
Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.DeterminantUnit
Langlands.Representation.CuspidalSupport.DualAveraging
Langlands.Representation.CuspidalSupport.GroupTransport
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.LeviGapVanishing
Langlands.Representation.CuspidalSupport.LeviSplitContraction
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
Langlands.Representation.Dual.Definitions
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.MultiplicityStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.GeometricLemmaStatement
Langlands.Representation.Geometric.IntersectionTransport
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Induction.BlockCharacterAbsorption
Langlands.Representation.Induction.BlockEquivalence
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactBilinearPairing
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactPairingDuality
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactScalarProof
Langlands.Representation.Induction.CompactScalarStatement
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.PiScalarIntegral
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Jacquet.BlockCompressionProof
Langlands.Representation.Jacquet.BlockCompressionStatement
Langlands.Representation.Jacquet.BlockPowerKernelProof
Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
Langlands.Representation.Jacquet.CanonicalLiftDefinitions
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement
Langlands.Representation.Jacquet.CanonicalLiftStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.OppositeCanonicalLiftProof
Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.RefinedOppositeCompressionProof
Langlands.Representation.Jacquet.RefinedOppositeCompressionStatement
Langlands.Representation.Jacquet.RefinedOppositePowerKernelProof
Langlands.Representation.Jacquet.RefinedOppositeStableImageProof
Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.Jacquet.StablePairingProof
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.AdmissibilityStatement
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
Langlands.Representation.Parabolic.NaturalInductionDualityProof
Langlands.Representation.Parabolic.NaturalInductionDualityStatement
Langlands.Representation.Parabolic.NaturalJacquetDualityProof
Langlands.Representation.Parabolic.NaturalJacquetDualityStatement
Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedInductionStatement
Langlands.Representation.Parabolic.OppositeRefinementDefinitions
Langlands.Representation.Parabolic.OppositeRefinementFunctors
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionAdmissibility
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.Schur.CountableDimensionProof
Langlands.Representation.Schur.CountableDimensionStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EmbeddingProof
Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.ExactProof
Langlands.Representation.Smooth.Contragredient.ExactStatement
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
Langlands.Representation.Smooth.Contragredient.InvariantPairingStatement
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.FixedVectors.LawsProof
Langlands.Representation.Smooth.FixedVectors.LawsStatement
Langlands.Representation.Smooth.FixedVectors.OrderProof
Langlands.Representation.Smooth.FixedVectors.OrderStatement
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.SmoothDual
Langlands.Representation.Tensor.SmoothDualInjectivityProof
Langlands.Representation.Tensor.SmoothDualInjectivityStatement
Langlands.Representation.Tensor.SmoothDualSurjectivityProof
Langlands.Representation.Tensor.SmoothDualSurjectivityStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.DualProof
Langlands.Representation.Twist.DualStatement
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothPartDefinitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

## Direct external import roots

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.GroupWithZero.Action
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Field.Subfield.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Cardinality
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Matrix.Normed
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.SchurComplement
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Dual
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.OpenPos
Mathlib.MeasureTheory.Measure.Regular
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.WithBot
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.Algebraic.LinearIndependent
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Group
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
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
