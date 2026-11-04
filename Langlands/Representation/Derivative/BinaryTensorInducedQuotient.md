# Actual derivative quotients for binary tensor induction

Author: Worker 357. This is an internal assembly of actual published maps.
It introduces no new assertion transcribed from the literature. Its purpose is
to keep the quotient map, its ordered tensor factors and its surjectivity as data.

## Interface and universes

The parameters are arbitrary `p : ℕ` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, its supplied `T : F.TopologicalData`, a bundled
continuous nontrivial unitary additive character `ψ` for that topology, and
positive ranks `k,m` with witnesses `hk,hm`. The field universe `uF` and carrier
universe `uV` are independent.

Let `A`, `B`, and `X` be actual smooth complex representations of respectively
`GL_k(F)`, `GL_m(F)`, and `GL_(k+m)(F)`, with carriers in `Type uV`.
Put `L = Shahidi.twoBlocks k m hk hm` and
`σ = binaryLeviTensor T hk hm A B`.
Assume `A.representation` and `B.representation` irreducible and both factors
admissible. Admissibility has the Library's all-open-subgroups convention.
Supply an actual nonzero complex-linear intertwiner

```
j : X.representation.IntertwiningMap
  (T.normalizedParabolicInduced L σ.representation)
```

The definition `binaryTensorDerivativeQuotientOfInducedMap T hk hm ψ`
returns exactly an actual smooth `GL_k(F)` morphism with retained surjectivity:

```
{q : ((generalLinearDerivative T ψ (k+m) m (Nat.le_add_left m k) ⋙
         generalLinearRankCast T (Nat.add_sub_cancel k m)).obj X) ⟶
       (firstFactorTopDerivative T ψ k m).obj (A,B) //
  Function.Surjective (SmoothRep.hom q)}
```

The domain is the published order-`m` derivative followed by equality transport
from rank `k+m-m` to `k`. The target carrier is literally
`A ⊗[ℂ] (topDerivative T ψ m).obj B`, and `GL_k` acts only on `A`.
Here `topDerivative` is the order-`m` derivative of `B`, followed by its rank
transport to `GL_0`. The entire top-derivative vector space is retained.
The induced target of `j` has carrier in `Type (max uF uV)`, as required by
actual induction; the derivative quotient and its target remain in `Type uV`.
No universe resizing is used. In a segment application one can instantiate
`uV` by `max uF uV₀`, retaining an independent original base universe `uV₀`.

There is no irreducibility, admissibility, finite-length or nontriviality premise
on `X`, no injectivity premise on `j`, and no nonvanishing, dimension or
irreducibility premise on the top derivative of `B`. In particular, the result
does not assert that the quotient is nonzero.

## Implemented construction

`binaryLeviTensor` is the actual indexed tensor object
`FiniteTensor.externalSmoothObject` on the dependent family
`Fin.cases A (Fin.cases B finZeroElim)` for the actual shape `L`.
Block zero is `A`; block one is `B`. Smoothness is the published smoothness of
finite external tensors. This definition has no asserted uniqueness or chosen
irreducible factorization premise.

`binaryLeviTensorPullbackIso` gives an actual smooth-category isomorphism from
`(positiveTwoBlockLeviPullback T k m hk hm).obj σ` to
`(exteriorTensor T k m).obj (A,B)`. Its linear equivalence is precisely the
published `Shahidi.pairSplit` on this dependent carrier family. The pullback
uses the inverse of the actual continuous two-block Levi equivalence; hence
the first Levi coordinate is `g.1` and the second is `g.2`.
`Shahidi.pairSplit_external` proves that the transported indexed action is
`TensorProduct.map (A.representation g.1) (B.representation g.2)`.
This is definitionally the raw exterior action. `SmoothRep.mkIso` then packages
the equivariant linear equivalence. No isomorphism classes are substituted.

`binaryLeviTensor_isIrreducible` supplies irreducibility of `σ`.
The two given irreducibility and admissibility proofs become the corresponding
factorwise proofs by finite case analysis. The published
`admissibleSchur_scalarEndomorphism` makes every factor self-intertwiner scalar.
The published `FiniteTensor.isIrreducible_external` applies to the actual
indexed external action. Its proof uses Jacobson density over the group
algebra: finite-coordinate endomorphisms isolate a nonzero tensor coefficient,
so every nonzero invariant submodule contains all pure tensors and equals the
whole tensor module. Scalar Schur itself restricts a self-intertwiner to an
open subgroup's finite-dimensional fixed space, obtains an eigenvector over
`ℂ`, and uses irreducibility to make that eigenvalue global. Neither input is
a segment representation theorem.

For the final definition, let `q` be the subtype returned by the published
`derivativeQuotientOfInducedMap` for `X`, `σ`, the just-proved irreducibility,
and `j`. That definition descends evaluation at the identity to the actual
normalized Jacquet module. Translating the source shows that nonzero `j`
gives a nonzero Jacquet evaluation; irreducibility of `σ` makes it onto.
Continuous Levi pullback preserves its linear map. The elementary quotient-lift
lemma makes the mapped partial derivative onto, and the independently proved
general derivative/Jacquet comparison identifies the source with the ordinary
derivative and the displayed rank transport. Thus `q` is an actual surjection
onto the partial derivative of the pulled-back `σ`.

Let `e` be `partialDerivative.mapIso` of
`binaryLeviTensorPullbackIso`. Let `t` be the component at `(A,B)` of the chosen
published natural isomorphism `partialDerivativeTensor F T ψ k m`.
The final returned morphism is literally

```
q.val ≫ e.hom ≫ t.hom
```

The map `q.val` is surjective by its subtype witness, and the other two maps
are surjective because they underlie actual isomorphisms. Composition proves
the retained `Function.Surjective` witness.

The tensor comparison used here has a general proof: the relation quotient on
the second tensor factor commutes with the binary tensor product by its two
universal properties. The all-rank top localization comparison then identifies
the full upper quotient with the normalized minus tower, with the explicit
rank transports. It uses no segment derivative formula. The Jacquet comparison
also constructs actual quotient equivalences and verifies their normalized
first-factor actions, rather than assuming its statement definition.

## Independence and provenance audit

The five direct imports are `Derivative.InducedMapQuotient`,
`Derivative.PartialDerivativeTensorProof`, `Tensor.FiniteProperties`,
`Smooth.Schur.Proof` and `Shahidi.IntertwiningInduced`, all under
`Langlands.Representation`. Every used declaration is in the supplied published
Library. This module imports no pending cut-embedding or other pending result.
At Library base `8a1c71c3b7e45f52546ca1d740fc0b623ffb6299`, recursive traversal of
the actual import declarations gives 166 project modules including this entry
and 125 distinct directly named external frontier imports. All 165 inherited
Lean/Markdown pairs match that Library byte for byte. No module or Markdown
is missing. The complete inventories follow below. The code scan finds no
host-excluded name, proof hole, new axiom or prohibited execution syntax.
These checks corroborate the inspected definitions and proof bodies; a list
of imports by itself is not a mathematical proof.

The actual used proof chain consists of smooth finite external tensors,
two-block Levi coordinate projection, the published indexed-to-binary tensor
linear equivalence and action identity, scalar Schur for admissible irreducible
representations, general tensor density, normalized Jacquet evaluation, the
actual quotient-lift surjectivity lemma, general normalized derivative/Jacquet
comparison, general binary tensor/localization comparison and categorical
composition. The quotient and tensor comparison modules record the full lower
quotient and normalization audits. The current used bodies and the inherited
fingerprints were checked again for this assembly.

The transitive Classification modules are only `Supercuspidal`,
`SupercuspidalContragredientStatement`, and `SupercuspidalContragredientAux`.
They enter through generic smooth contragredient infrastructure imported by
`Shahidi.IntertwiningInduced`, which supplies `pairSplit`. No contragredient or
supercuspidal theorem is a step of the new constructor. The auxiliary module's
generic admissibility/irreducibility reflection results use compact fixed-vector
duality and annihilators, not any segment classification. There is no
individual head, segment, socle, segment derivative or segment Jacquet module
in the closure. The unused analytic intertwining constructions do not supply
an analytic theorem premise.

The following restrictions are retained directly and transitively:

- No parent `GenericSegmentProductUniqueness`, full head-product criterion in
  either direction, multisegment exhaustion, ordered strong-head existence,
  quotient coverage, ordered conversion, tempered uniqueness, square-integrable
  classification or exhaustion, or regular exhaustion conclusion is used.
- No Ze80 3.5 or 9.6, their proof successors, segment/head/socle derivative or
  Jacquet formulas, segment-socle product criterion or linked-product structure
  conclusion is used. No segment-socle part of
  `8e5b4563-0365-41c7-b134-70f2a0b36292` occurs.
- No `SegmentHeadSupportStep`, `SegmentHeadJacquetReduction`,
  `SegmentSocleJacquetReduction`, `core_mid`, two-supercuspidal reducibility,
  `TwoSupercuspidalProductStructureProof`, or restricted support-proof
  intermediate is imported or consumed.
- No proposition definition, draft, pending proof, source citation or downstream
  classification is treated as an already proved input.

Operator decisions `bd71b9185aab5d6eafffb7891bd3a3ca`
and `0edda6122ce65ed7ac51603c37473920`
permit independently proved general derivative theory and the general Ze80
3.7(b) comparison used by `InducedMapQuotient`, while preserving the host's
exclusions. The tensor comparison is likewise proved from quotient universal
properties and the actual normalized minus tower. The further rulings
`30144f6f9b59540b88b6d4c1517892d9`, `ed80148e21e7523abfc048f455e98eb0`,
`2b33898bdd0a5ff1b9031be5155a06f0` and `ca18fd5005bf5e12a3f7cade18dca865`
are respected without invoking their restricted support or reducibility
exceptions. All six trusted operator messages were read completely. No run
control, owner pause or review independence is waived.

This focused pair is a prerequisite construction. It proves no segment
nonvanishing, truncated-head identification, derivative irreducibility,
multiplicity formula or product criterion. In particular, the host's full
`SegmentHeadProductIrreducibility` equivalence and its linked converse remain
separate unproved obligations.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

## Complete transitive project inventory

```
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockUnipotent
Langlands.Group.GL.Blocks
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
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
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperUnipotent
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.SmoothWeakIntegral
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Contragredient
Langlands.Representation.Category.Twist
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Conductor.Congruence
Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
Langlands.Representation.Derivative.BinaryTensorInducedQuotient
Langlands.Representation.Derivative.InducedMapQuotient
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement
Langlands.Representation.Derivative.PartialDerivativeJacquetLHS
Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization
Langlands.Representation.Derivative.PartialDerivativeJacquetRHS
Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison
Langlands.Representation.Derivative.PartialDerivativeTensorLocalization
Langlands.Representation.Derivative.PartialDerivativeTensorProof
Langlands.Representation.Derivative.PartialDerivativeTensorStatement
Langlands.Representation.Derivative.PartialLocalizationCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Derivative.TopLocalizationBoundary
Langlands.Representation.Derivative.TopLocalizationComparison
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.TopLocalizationMirabolicZero
Langlands.Representation.Derivative.TopLocalizationRestriction
Langlands.Representation.Derivative.TopLocalizationStep
Langlands.Representation.Dual.Definitions
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.IntertwiningCovariance
Langlands.Representation.Shahidi.IntertwiningInduced
Langlands.Representation.Shahidi.IntertwiningIntegral
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.Schur.Proof
Langlands.Representation.Smooth.Schur.Statement
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
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
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
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.Nonarchimedean.Subgroup
```

## Directly named external frontier imports

```
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.AddChar
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.CategoryTheory.Whiskering
Mathlib.Data.Fin.Rev
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
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
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Trace.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.LinearCombination
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
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Order.Compact
Mathlib.Topology.UrysohnsLemma
```
