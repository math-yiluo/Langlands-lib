import Langlands.GroupScheme.Rational.RootSubgroupCentrality
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Rational.RelativeRootMultiples

/-! # Conditional assembly of the exact relative-root vector statement -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The exact general source statements suffice for the existing vector and
central fppf quotient target, at every field and scheme universe. -/
def RootSubgroupVectorReductionStatement : Prop :=
  RelativeRootSystemStatement.{u} → SemigroupRealizationStatement.{u} →
    SemigroupCommutatorStatement.{u} → CyclicRootFunctorComparisonStatement.{u} →
      CyclicWeightFiltrationStatement.{u} → RootSubgroupVectorStatement.{u}

/-- Assemble the two target branches from the existing general source statements.
All five structural statements remain explicit hypotheses of this reduction. -/
theorem rootSubgroupVectorReduction : RootSubgroupVectorReductionStatement.{u} := by
  intro hroots hreal hcomm hcyclic hfilter k _ G hG S i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro a ha
  have ha0 : a ≠ 0 := ha.1
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hR : HasRelativeRootSystem i := hroots k G hG S i hi
  have hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i :=
    fun _ hn => hR.nsmul_not_mem_of_three_le ha hn
  let b := AutomorphicAction.conjugation i
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    hcyclic k G hG.smooth hG.isAffineHom S hS i a ha0
  constructor
  · intro h2 U j hj
    let := hj.1
    have hj' : (weightFiltration b a 1).IsRepresentedBy j := by
      rw [hfirst]
      exact hj
    obtain ⟨V, q, c, d, hq, hV, _, _⟩ :=
      (hfilter k G hG.smooth hG.isAffineHom S hS b a ha0 1 (by omega)).2 U j hj'
    have htwo : weightFiltration b a 2 = ⊥ :=
      weightFiltration_two_eq_bot_of_noDoubleRoot hreal hG.smooth hS i ha0 h2 hhigh
    have hq' : IsFppfQuotient ⊥ q := by
      simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
        SubgroupFunctor.comap_bot_of_mono] using hq
    exact hq'.isVectorGroup_of_bot hV.isVectorGroup
  · intro _
    have hcentral := hasCentralDoubleSubgroup_of_noHigherRoots
      hreal hcomm hcyclic hG.smooth hS i ha0 hhigh
    refine ⟨hcentral.1, hcentral.2, ?_⟩
    intro U j hj
    have hj' : (weightFiltration b a 1).IsRepresentedBy j := by
      rw [hfirst]
      exact hj
    obtain ⟨V, q, c, d, hq, hV, _, _⟩ :=
      (hfilter k G hG.smooth hG.isAffineHom S hS b a ha0 1 (by omega)).2 U j hj'
    have hweights : ∀ n : ℕ, 3 ≤ n → n • a ∉ actionWeightSupport b ⊤ := by
      intro n hn hsupp
      exact hhigh n hn ((mem_actionWeightSupport_conjugation_iff i
        (hS.nsmul_ne_zero ha0 (by omega))).mp hsupp)
    have htwo : weightFiltration b a 2 = subgroup i (2 • a) := by
      rw [weightFiltration_two_eq_double b a hweights]
      exact hcyclic k G hG.smooth hG.isAffineHom S hS i (2 • a)
        (hS.nsmul_ne_zero ha0 (by omega))
    refine ⟨V, q, ?_, hV.isVectorGroup⟩
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo] using hq

end Langlands.GroupScheme.RelativeRoot
