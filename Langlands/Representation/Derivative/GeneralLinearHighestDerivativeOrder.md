# Choosing a highest positive general-linear derivative order

Worker 357. Internal construction from the published actual derivative functors,
their positive-order detection theorem, and a bounded maximum in the natural
numbers. No new original-source assertion is made.

For positive rank `N` and any actual nonzero smooth complex representation `A`
of `GL_N`, the structure `GeneralLinearHighestDerivativeOrderData` retains an
order `k`, its feasibility and positivity, nontriviality of the actual `k`-th
derivative, and subsingleton carriers for every higher feasible derivative.
The field and carrier universes are independent. No finite-length, admissibility,
irreducibility, or segment hypothesis is imposed.

The constructor `chooseGeneralLinearHighestDerivativeOrder` takes the bounded
`Nat.findGreatest` of orders with nontrivial derivative. Order zero belongs to
that predicate because the zeroth derivative is definitionally the identity.
The maximum therefore has nontrivial derivative. Maximality rules out a
nontrivial higher derivative, giving its subsingleton carrier. The published
`highestGeneralLinearDerivativeOrder_pos` then gives positivity: if the maximum
were zero, positive-derivative detection would force the source itself to vanish.

The constructor uses `Classical.choice` through the greatest-order witness's
`choose_spec`. The returned feasibility proof may be the separate bound
`Nat.findGreatest_le`; proof irrelevance makes the actual derivative independent
of which proof of the same inequality is supplied. The output remains an actual
derivative of `A`, indexed by the retained natural number.

This unit does not construct a derivative constituent, quotient, support, or
comparison isomorphism. It does not prove either direction of the special-head
product criterion. In particular no irreducibility assertion about the highest
derivative is made. Although a finite-length consumer can later use general
derivative finite-length preservation, that theorem is unnecessary here.

## Mathematical dependency and independence audit

The direct imports are
`Langlands.Representation.Classification.HighestDerivativeSupportShiftBoundary`
and `Mathlib.Data.Nat.Find`. The constructor uses the following declarations:

| Input | Use |
| --- | --- |
| `generalLinearDerivative` | The actual order-indexed derivative; order zero is definitionally the identity. |
| `Nat.findGreatest`, `Nat.findGreatest_le`, `Nat.findGreatest_spec`, `Nat.findGreatest_is_greatest` | Bounded selection and its defining properties, with the predicate made decidable classically. |
| `not_nontrivial_iff_subsingleton` | Converts absence of a nontrivial higher carrier to its vanishing. |
| `highestGeneralLinearDerivativeOrder_pos` | Makes the selected feasible, nonzero, highest order positive at positive source rank. |

The last input is an actual published theorem. Its proof reduces order zero to
the identity functor, restricts to the actual mirabolic subgroup, and uses
`Mirabolic.subsingleton_of_forall_mirabolicDerivative`. That vanishing theorem
proves joint detection by rank induction, with a trivial-radical boundary and
the independently proved `subsingleton_of_psiMinus_phiMinus` step. The latter
uses general relation quotients, finite character means and Fourier
orthogonality. This is general derivative infrastructure; no segment formula
occurs. `Homogeneity` supplies derivative and level definitions, with no
homogeneity theorem assumed in this proof.

The boundary module also contains elementary rank-zero support lemmas. Those
lemmas are unused here. Its support imports account for all six classification
modules in this closure: `ConstituentRelations`,
`HighestDerivativeSupportShiftBoundary`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport`, and `SupercuspidalTwist`. Apart from the boundary's
general derivative positivity theorem, these supply actual data, predicates
and elementary transport constructions. They supply no head or socle
existence, classification, segment derivative, or product criterion.
The lower Whittaker and Rankin–Selberg files supply character, lattice and
quotient constructions in the detection route; no classification or generic
product conclusion is applied.

The recursive audit at Library
`e9121d2f8e2a84b24a5c3d710d82082ab261845c` finds 104 project modules including
this new module, and 88 distinct direct external import roots. All 103 inherited
Lean/Markdown pairs match that exact published Library byte for byte. No import
or Markdown pair is missing. A scan against the host and inherited excluded
task/declaration identifiers has no code hits. The closure has no proof holes,
new axioms or prohibited command/tactic syntax. The mathematical route above,
in addition to that scan, rules out reuse of a renamed excluded conclusion.

Specifically absent are `GenericSegmentProductUniqueness`; multisegment and
square-integrable or regular exhaustion; ordered head existence, quotient
coverage and conversion; tempered uniqueness;
`SquareIntegrableLanglandsClassification`; special-head product irreducibility
in either direction; all excluded segment-socle existence, gluing,
commutation and product criteria; segment full, head, or socle Jacquet
formulas; segment exponent-norm formulas; analytic segment classification;
Zelevinsky 1980 §§3.5 and 9.6, their proof successors, and any full derivative
formula. No segment-socle portion of task
`8e5b4563-0365-41c7-b134-70f2a0b36292` enters this closure. The full
two-supercuspidal product structure is absent, and even the narrowly permitted
adjacent reducibility import is unnecessary here. The support proof's
restricted `core_mid` and `core` steps are neither imported nor applied.

This is consistent with the general derivative permission in the complete
operator messages
`/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md`
and
`/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md`.
The narrower permissions and retained limits in
`/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md`,
`/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md`,
`/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md`
and
`/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md`
are preserved and are not needed as extra mathematical inputs here.
All six trusted operator messages were read in full. Neither pending quotient
nor pending shifted-support construction supplies an input to this unit.
The exact full host criterion remains open.

## Full project import inventory

```text
Langlands.Analysis.Local.QuotientMeasure
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
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
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.LocalFactor.Harmonic.Statement
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
Langlands.Representation.Classification.HighestDerivativeSupportShiftBoundary
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
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
Langlands.Representation.Tensor.Finite
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
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.Operations
```

## Full direct external import inventory

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.FieldTheory.Finite.Basic
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Regular
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
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Quotient
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
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Basic
```
