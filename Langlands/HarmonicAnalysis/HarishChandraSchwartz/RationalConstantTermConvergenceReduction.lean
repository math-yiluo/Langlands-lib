import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceReductions
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises

/-! # Radical convergence and the vanishing comparison from Proposition II.4.5

This module reduces the closed targets `RationalSchwartzConstantTermConvergenceStatement` and
`RationalCuspidalVanishingComparisonStatement` (module `RationalCuspidalConvergenceStatements`)
to two published propositions, named as hypotheses:

* `RationalConstantTermEstimateStatement` (Waldspurger, Proposition II.4.5 on actual points);
* `JointSpecialCompactBasisExistenceStatement` (the special compact subgroup of Renard V.5.1
  with its simultaneous basis, V.5.2).

The reduction is recorded as the proposition `RationalConstantTermConvergenceReductionStatement`
and proved here (`rationalConstantTermConvergenceReduction`). Once both hypotheses are proved, the
two targets are applications of
`RationalConstantTermEstimateStatement.schwartzConstantTermConvergence` and
`RationalConstantTermEstimateStatement.cuspidalVanishingComparison`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- **Radical convergence from Proposition II.4.5 and the joint special compact subgroup.**
`RationalConstantTermEstimateStatement` and `JointSpecialCompactBasisExistenceStatement` imply
`RationalSchwartzConstantTermConvergenceStatement`: for every actual Schwartz function `f`, every
standard `P_J = M_J U_J`, every Haar measure on `U_J(F)` and all `x, y ∈ G(F)`, the function
`v ↦ f(x v y)` is integrable on `U_J(F)`. -/
theorem RationalConstantTermEstimateStatement.schwartzConstantTermConvergence
    (h : RationalConstantTermEstimateStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) :
    RationalSchwartzConstantTermConvergenceStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ f I _ muU _ x y
  obtain ⟨K0, hK0o, hK0c, hPK0, hbasis, hcover, hLevi⟩ :=
    exists_constantTermPremises_of_joint hJoint hG hi hν
  have hJ := Aubert.General.RationalPointFamily.rootSet_subset i ν I
  obtain ⟨hLcover, hM0⟩ := hLevi _ hJ
  exact h.integrable_mul_mul hG hi hν hJ hK0o hK0c hbasis hcover hLcover hK0o hK0c hPK0 hM0
    K.isOpen hKc hPK hρ muU (Space.coe_mem f) x y

/-- **The vanishing comparison from Proposition II.4.5 and the joint special compact
subgroup.** `RationalConstantTermEstimateStatement` and
`JointSpecialCompactBasisExistenceStatement` imply `RationalCuspidalVanishingComparisonStatement`:
an actual Schwartz function lies in the cuspidal submodule if and only if all its normalized
standard constant terms along proper standard parabolics vanish. -/
theorem RationalConstantTermEstimateStatement.cuspidalVanishingComparison
    (h : RationalConstantTermEstimateStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u}) :
    RationalCuspidalVanishingComparisonStatement.{u} :=
  (h.schwartzConstantTermConvergence hJoint).vanishingComparison

/-- **The reduction of the radical convergence and vanishing comparison targets.** Proposition
II.4.5 on actual points (`RationalConstantTermEstimateStatement`) and the joint special compact
subgroup (`JointSpecialCompactBasisExistenceStatement`) imply both
`RationalSchwartzConstantTermConvergenceStatement` and
`RationalCuspidalVanishingComparisonStatement`. -/
def RationalConstantTermConvergenceReductionStatement : Prop :=
  RationalConstantTermEstimateStatement.{u} → JointSpecialCompactBasisExistenceStatement.{u} →
    RationalSchwartzConstantTermConvergenceStatement.{u} ∧
      RationalCuspidalVanishingComparisonStatement.{u}

/-- Proof of `RationalConstantTermConvergenceReductionStatement`. -/
theorem rationalConstantTermConvergenceReduction :
    RationalConstantTermConvergenceReductionStatement.{u} := fun h hJoint =>
  ⟨h.schwartzConstantTermConvergence hJoint, h.cuspidalVanishingComparison hJoint⟩

end Langlands.HarishChandraSchwartz
