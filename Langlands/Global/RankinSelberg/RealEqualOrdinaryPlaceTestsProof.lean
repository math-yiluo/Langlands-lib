import Langlands.Global.RankinSelberg.ArchimedeanFactorizationOrdinaryReduction
import Langlands.Global.RankinSelberg.RealEqualOrdinaryDescent
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryPlaceTestsProof

/-! # Nonvanishing of ordinary equal-rank integrals at real places -/

noncomputable section

open NumberField
open scoped CategoryTheory.MonObj Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean (matrixModel rightDerivative)
open Langlands.Automorphic Langlands.Global.HeckeFunctionalEquation
open ArchimedeanLocal RealEqualOrdinaryDescent RealUnequalPositiveRank RealUnequalRankZero
open RealUnequalFamily (HasLeftCharacter)
open RealWhittakerTranslatedMellin (HasGaugeBound hasGaugeBound_of_mem_model)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

set_option maxHeartbeats 1800000 in
/-- Actual real-place Whittaker restrictions supply an ordinary equal-rank test
nonzero arbitrarily far to the right in every rank above one. -/
theorem realEqualOrdinaryPlaceTestsPositiveRank : RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  intro T T' v a ha d d' hd hd'
  let r := n + 1
  have htr : n < r := Nat.lt_succ_self n
  obtain ⟨A, B, -, hB, ⟨f, hf⟩, hval⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).1 v d hd a ha
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ := by
    rw [← complex_inverseCharacter]
    exact isStandardAdditiveCharacter_of_unitary _ (inverseCharacter_rational ψ hψ)
  obtain ⟨x', hx'⟩ := cuspidalWhittakerIdentityNonzero F r T' ψ.complex⁻¹ hstd'
  let V : Langlands.GeneralLinear (r + 1) ℝ → ℂ := fun g =>
    cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (r + 1) v g * finitePoint F (r + 1) 1)
  have hVact : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v V := ⟨x', 1, rfl⟩
  have hBact (g : realStandardKFinite (r + 1) d) : IsRealPlaceWhittaker F T ψ.complex v (B g) := by
    refine ⟨A g, 1, funext fun k => ?_⟩
    rw [hval, mul_finitePoint_one]
  have hVmem := (realPlaceUniformWhittakerModel F ψ hψ r T' v a ha d' hd' V).2 hVact
  have hVreg := realUniformWhittakerRegularity r d' (-a) V hVmem
  have hVl : HasLeftCharacter (-a) V := (hVreg.1 []).1
  have hVc : Continuous V := (hVreg.1 []).2.1.continuous
  have hVg : HasGaugeBound V := hasGaugeBound_of_mem_model hVmem
  have hBg (g : realStandardKFinite (r + 1) d) : HasGaugeBound (B g) :=
    hasGaugeBound_of_mem_model ((realPlaceUniformWhittakerModel F ψ hψ r T v a ha d hd (B g)).1
      (hBact g))
  by_contra hcon
  push Not at hcon
  let V₁ : Langlands.GeneralLinear (n + 1) ℝ → ℂ := fun g => V (padGL (Nat.le_succ (n + 1)) g)
  have hV₁l : HasLeftCharacter (-a) V₁ := hasLeftCharacter_padGL htr.le hVl
  have hV₁c : Continuous V₁ := hVc.comp (UnequalAnalytic.continuous_padGL _)
  have hV₁g : HasGaugeBound V₁ := hasGaugeBound_padGL htr.le hVg
  have htop (g : realStandardKFinite (r + 1) d) : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realUnequalIntegral htr (realQuotientMeasureData n) (B g) V₁ s = 0 :=
    realEqualOrdinaryDescent n (realQuotientMeasureData n) (realQuotientMeasureData r) a (B g) V
      (hB.1 g) hVl (hB.2.1 g).continuous hVc (hBg g) hVg
      (fun Φ => hcon (B g) V Φ (realQuotientMeasureData r) (hBact g) hVact)
  have hall := descent_to_rankZero htr hB hBg hV₁l hV₁c hV₁g htop
  have h0 : 0 < r := Nat.zero_lt_succ n
  let V₀ : Langlands.GeneralLinear 1 ℝ → ℂ := fun g => V₁ (padGL (Nat.succ_le_succ (Nat.zero_le n)) g)
  have hV₀l : HasLeftCharacter (-a) V₀ := hasLeftCharacter_padGL (Nat.zero_le n) hV₁l
  have hV₀c : Continuous V₀ := hV₁c.comp (UnequalAnalytic.continuous_padGL _)
  have hV₀g : HasGaugeBound V₀ := hasGaugeBound_padGL (Nat.zero_le n) hV₁g
  let X := firstRootDirection h0
  let fX : realStandardKFinite (r + 1) d :=
    ⟨rightDerivative (matrixModel ℝ (r + 1)) X f,
      Langlands.Archimedean.rightDerivative_mem_kFiniteFunctions_realStandardModule _ _ f.2 X⟩
  have hBX : B fX = rightDerivative (matrixModel ℝ (r + 1)) X (B f) := hB.2.2.2.2 X f fX rfl
  let D₀ := realQuotientMeasureData 0
  obtain ⟨σ, hint⟩ := exists_integrable h0 D₀ (hB.1 f) hV₀l
    (hB.2.1 f).continuous hV₀c (hBg f) hV₀g
  obtain ⟨σX, hintX⟩ := exists_integrable h0 D₀ (hB.1 fX) hV₀l
    (hB.2.1 fX).continuous hV₀c (hBg fX) hV₀g
  obtain ⟨τ, hz⟩ := hall f
  obtain ⟨τX, hzX⟩ := hall fX
  rw [hBX] at hintX hzX
  have hzero := value_eq_zero_of_integrals_eq_zero h0 D₀ (hB.2.1 f) (hB.1 f) hV₀c
    (σ₀ := max σ σX) (fun s hs => hint s ((le_max_left _ _).trans_lt hs))
    (fun s hs => hintX s ((le_max_right _ _).trans_lt hs)) hz hzX
  have hV₀one : V₀ 1 = cuspWhittaker F T' ψ.complex⁻¹ x' 1 := by
    change cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (r + 1) v
      (padGL _ (padGL _ 1)) * finitePoint F (r + 1) 1) = _
    rw [map_one, map_one, mul_finitePoint_one, realPlacePoint_one]
  rw [hf, one_mul, hV₀one] at hzero
  exact hx' hzero

end Langlands.Global.RankinSelbergGlobal
