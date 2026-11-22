import Langlands.Global.Factors.CuspidalPairPoleEqualBoundedTests

/-! # Equal-rank strip bounds from bounded sums of actual partial tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField Set Filter
open scoped Classical CategoryTheory.MonObj Topology

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal RankinSelbergGlobal.EqualAnalytic
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u,uQ} T} {P' : CuspidalSpectralPresentation.{u,uQ} T'}
  {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' hP hP'} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {Linf Λ : ℂ → ℂ} {poleCondition : Prop}

local instance eqBoundedCompletionAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance eqBoundedCompletionSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

private theorem not_exceptional_of_re {s : ℂ} (hs : 1 < s.re) :
    s ∉ ({0, 1} : Set ℂ) := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨fun h => by norm_num [h] at hs, fun h => by norm_num [h] at hs⟩

/-- For an equal-rank completion with the two-point pole profile, a bounded sum
of normalized ordinary partial tests transfers the strip bounds of the actual
global integrals. -/
def EqualStripBoundFromBoundedTestsStatement (c : FinitePairLChoice P P' hP hP')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf Λ : ℂ → ℂ) (poleCondition : Prop) : Prop :=
  (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  P.exceptional ⊆ S → P'.exceptional ⊆ S → FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  HasCoveringEqualPartialTests c S ψ Linf →
  HasBoundedEqualPartialTests c S ψ Linf →
  c.IsCompletedLFunction Linf Λ → HasSimplePoleProfile Λ poleCondition → IsBoundedInVerticalStrips Λ

theorem equalStripBoundFromBoundedTests : EqualStripBoundFromBoundedTestsStatement c S ψ Linf Λ poleCondition := by
  intro hψ hPS hP'S hS hT hT' hCov hBound hΛ hp
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨ω', hω', _⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  obtain ⟨J, test, hSum⟩ := hBound
  let D := equalNormalizedFamily c hCov
  let j (i : J) : D.Test := test i
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  choose σ I hI hIb hIr using fun i : J =>
    equalIntegral_splitCentre_continuation T T' hT hT' hω hω' ψ.complex hstd
      (test i).1.left (test i).1.right (test i).1.schwartz (test i).1.schwartz_mem
  refine isBoundedInVerticalStrips_of_bounded_normalized_sum I (fun i => (test i).2.value) Λ hSum ?_ hIb
  intro i s hs
  have hJ := regularizeSimplePoles_spec (hIr i).1
    (fun p hp => ⟨((hIr i).2 p hp).1, ((hIr i).2 p hp).2.1⟩)
  have hK := regularizeSimplePoles_spec hp.1 (fun p hm => ⟨(hp.2 p hm).1, (hp.2 p hm).2.1⟩)
  obtain ⟨a, ha⟩ := D.integral_eq_on_right hψ hPS hP'S hS hω hω' (j i)
  obtain ⟨b, hb⟩ := hΛ
  let β := max (max (σ i) a) (max b 1)
  let z : ℂ := (β + 1 : ℝ)
  have hz : β < z.re := by change β < β + 1; linarith
  have he : regularizeSimplePoles (I i) =ᶠ[𝓝 z]
      (fun q => (test i).2.value q * regularizeSimplePoles Λ q) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with q hq
    have hleft := (le_max_left _ _).trans_lt hq
    have hright := (le_max_right _ _).trans_lt hq
    have hnot := not_exceptional_of_re ((le_max_right b 1).trans_lt hright)
    obtain ⟨_, _, hprod, hval⟩ := hb q ((le_max_left b 1).trans_lt hright)
    have hRight := ha q ((le_max_right (σ i) a).trans_lt hleft)
    change equalIntegral F (ω * ω') (cuspFunction F T (test i).1.left)
      (cuspFunction F T' (test i).1.right) (test i).1.schwartz q =
        (test i).2.value q * (Linf q * ∏' v, c.finiteL v q) at hRight
    rw [hJ.2.1 q hnot, hK.2.1 q hnot, (hI i q ((le_max_left (σ i) a).trans_lt hleft)).2,
      hRight, hval, hprod.tprod_eq]
    ring
  have hEqual := congrFun (hJ.1.eq_of_eventuallyEq ((test i).2.analytic.mul hK.1) he) s
  have hm : s ≠ 0 ∧ s ≠ 1 := by simpa only [mem_insert_iff, mem_singleton_iff, not_or] using hs
  rw [hJ.2.1 s hs, hK.2.1 s hs, mul_left_comm ((test i).2.value s)] at hEqual
  exact mul_left_cancel₀ (mul_ne_zero hm.1 (sub_ne_zero.mpr hm.2)) hEqual

end Langlands.Global.CuspidalPairPoles
