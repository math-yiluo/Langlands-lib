# Derivative quotients from maps into normalized induction

Author: Worker 357. This is an internal construction from published general
representation-theoretic maps. It has no external source claim. Its purpose is
to retain the actual quotient intertwiner that follows by evaluating a nonzero
map into normalized induction, then taking partial derivatives.

## Parameters and actual objects

The field and carrier universes `uF` and `uV` remain independent. The construction
works for every prime `p`, every `F : PadicField.{uF} p`, every supplied topology
`T : F.TopologicalData`, and every bundled continuous nontrivial unitary
additive character `ψ` for that topology. No additional character hypothesis
is imposed.

Let `k,m>0`, let `B=Shahidi.twoBlocks k m hk hm`, let `X` be an actual smooth
complex representation of `GL_(k+m)` with carrier in `Type uV`, and let `σ` be
an actual smooth complex representation of the actual block-diagonal group
`B.Levi F.Carrier`, again with carrier in `Type uV`. Assume `σ` irreducible and
supply an actual nonzero intertwiner

\[
 j:X\longrightarrow i_B(\sigma).
\]

There is no irreducibility, finite-length, admissibility or injectivity premise
on `X` or on `j` beyond the stated smoothness and nonzero condition.

`positiveTwoBlockLeviPullback` is the continuous pullback functor along the
inverse of `Shahidi.twoBlockLeviContinuousEquiv`. Write `P` for it. Its objects
are actual representations of `GL_k × GL_m`; it preserves the carriers and the
underlying linear maps. In particular the actual product-group object is
`P.obj σ`, rather than an unspecified tensor factorization of `σ`.

`derivativeQuotientOfInducedMap` returns a subtype whose first projection is
an actual morphism of smooth `GL_k` representations

\[
 q:\operatorname{cast}_{k+m-m=k}(D_mX)
       \longrightarrow\partial_m(P\sigma),
\]

and whose second projection proves `Function.Surjective (SmoothRep.hom q)`.
The domain is literally the object at `X` of
`generalLinearDerivative T ψ (k+m) m (Nat.le_add_left m k) ⋙
generalLinearRankCast T (Nat.add_sub_cancel k m)`. The target is literally
`(partialDerivative T ψ k m).obj (P.obj σ)`. The definition retains the chosen
intertwiner and its surjectivity, without selecting an isomorphism class or
claiming irreducibility or nonvanishing of that target.

## Construction and proof

The grouped elementary lemma `partialDerivative_map_surjective` works for all
natural `k,m`, including zero. For any actual smooth product-group morphism
`f:A→B` whose underlying map is surjective, it proves that the mapped partial
derivative is surjective. Given a target quotient vector, first lift it to a
vector `v` of `B` with `partialDerivativeMk_surjective`, then lift `v` to `w`
of `A` using the supplied surjectivity. The class of `w` maps to the required
class by `partialDerivative_map_mk`. This uses the actual relation quotient;
it does not require a general exactness or filtration theorem.

For the main construction, `CuspidalSupport.jacquetEvaluation` evaluates `j`
at the identity and descends to the actual normalized Jacquet module. Its
published `jacquetEvaluation_ne_zero` theorem makes the resulting Levi
intertwiner `f:r_BX→σ` nonzero. This is the evaluation part of first
adjointness. The general proof uses covariance with the positive half modulus
in induction and the inverse half modulus in the normalized Jacquet action,
and proves nonzeroness by translating the source and evaluating the original
induced function at every group element. There is no hypothesis on a Jacquet
formula for `X`.

Install the supplied irreducibility of `σ` as an instance. Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero` then makes `f` surjective.
The proof of that general result passes to a linear map of group-algebra
modules with a simple target.

View `f` as a smooth-category morphism and apply `P.map`. By the actual
definition of continuous pullback, the resulting map `fp` has exactly the same
underlying linear map, hence is surjective. Its source is definitionally
`(positiveTwoBlockNormalizedJacquet T k m hk hm).obj X`, since that functor is
the normalized Jacquet functor followed by the same `P`.

Choose the published natural isomorphism supplied by
`partialDerivativeJacquetComparison F T ψ k m hk hm`. Its component `e` at `X`
has the rank-transported ordinary derivative as source and the partial derivative
of that actual transported Jacquet module as target. The returned morphism is
exactly

```
e.hom ≫ (partialDerivative T ψ k m).map fp
```

The grouped lemma proves surjectivity of the second factor. The underlying
representation equivalence `SmoothRep.equivOfIso e` proves surjectivity of
the first factor. Their composition gives the subtype's retained proof.
This is a definition returning data, not an assumed proposition or a replacement
statement for a missing mathematical theorem.

## Dependency and independence audit

The two direct imports are
`Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof`
and `Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation`.
The latter is the smaller published evaluation module; the full natural
first-adjointness module and its refined-Levi constructions are unnecessary.
The generic comparison constructs its natural isomorphism from the actual
left and right quotient equivalences and normalized actions. It does not
assume the truth of its Prop-valued statement.

At Library base `071b82c1a715daffe0334ad25311484eaba312b0`, the transitive closure
contains 102 project modules including this new root, and 89 distinct directly
named external imports. There are no missing modules or missing paired
Markdown files. Every inherited Lean/Markdown pair agrees byte for byte with
the supplied Library. All inherited modules are covered by the earlier
shifted-support dependency audit. Comparing those fingerprints finds only the
published addition `BlockShape.coordinateBlock` in `Group.GL.Blocks`: it is
literally the first projection of `B.indexEquiv.symm x`, and is not a mathematical
input to this construction. The current native inventory and source/proof
inspection found no exclusion-name matches, proof holes or prohibited execution
syntax. The complete current module inventories are below; inventory alone is
not used as evidence of a mathematical proof.

In particular the closure has no classification module, no individual-segment
construction, no segment/head/socle Jacquet or derivative formula, no segment
product criterion in either direction, and no multisegment or analytic
classification input. It does not use `SegmentHeadJacquetReduction`,
`SegmentSocleJacquetReduction`, Ze80 3.5/9.6 or their proof successors, the
segment-socle part of task `8e5b4563-0365-41c7-b134-70f2a0b36292`, or any of the
host's excluded parent uniqueness, exhaustion, ordered existence, coverage,
conversion, tempered or square-integrable classification conclusions. It
contains no `core_mid`, restricted length-two segment derivative argument,
`TwoSupercuspidalProductStructureProof`, or two-supercuspidal product proof.
The proof uses neither the pending unlinked-head-product construction nor any
other pending mathematical result.

The use of the published general positive two-block comparison is within the
operator decisions `bd71b9185aab5d6eafffb7891bd3a3ca` and
`0edda6122ce65ed7ac51603c37473920`, which permit independently proved general
derivative theory and the general Ze80 3.7(b) comparison while retaining the
host exclusions. The subsequent support-only rulings
`30144f6f9b59540b88b6d4c1517892d9`, `ed80148e21e7523abfc048f455e98eb0`,
`2b33898bdd0a5ff1b9031be5155a06f0` and `ca18fd5005bf5e12a3f7cade18dca865`
remain respected: this adapter uses none of the restricted support-proof
intermediates or reducibility imports at all.

This focused contribution adds only this pair. It leaves the full
`SegmentHeadProductIrreducibility` equivalence, including the linked converse,
as an outstanding host obligation. It neither proves nonvanishing for a
particular segment derivative nor assumes that a special head embeds into any
particular two-factor induction.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

## Full project closure

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
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Twist
Langlands.Representation.Conductor.Congruence
Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
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
Langlands.Representation.Derivative.PartialLocalizationCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Dual.Definitions
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
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
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
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.CompactNormCharacter
Langlands.Topology.Nonarchimedean.Subgroup
```

## Directly named external imports in the closure

```
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
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
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Matrix.Block
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Regular
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
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Trace.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.LinearCombination
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
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
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.Order.Compact
Mathlib.Topology.UrysohnsLemma
```
