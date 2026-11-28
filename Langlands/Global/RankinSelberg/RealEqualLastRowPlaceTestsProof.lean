import Langlands.Global.RankinSelberg.RealEqualLastRowDescent
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryPlaceTestsProof
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationOrdinaryReduction
import Langlands.Global.RankinSelberg.ArchimedeanActualWhittakerIntertwiners
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures

/-! # Ordinary nonvanishing for equal ranks at a real place -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic HeckeFunctionalEquation ArchimedeanLocal
open Langlands.Archimedean (rightDerivative matrixModel)
open RealUnequalFamily (HasLeftCharacter)
open RealWhittakerTranslatedMellin (HasGaugeBound hasGaugeBound_of_mem_model)
open RealUnequalPositiveRank (descent_to_rankZero hasLeftCharacter_padGL hasGaugeBound_padGL)
open RealUnequalRankZero (firstRootDirection value_eq_zero_of_integrals_eq_zero
  realPlacePoint_one mul_finitePoint_one)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

private abbrev G (k : ℕ) := Langlands.GeneralLinear (k + 1) ℝ

/-- For two actual cuspidal realizations on `GL_(r+1)` with `0 < r`, there are real-place
Whittaker restrictions and a Schwartz test whose ordinary integral is nonzero somewhere
in every right half-plane. -/
theorem realEqualOrdinaryPlaceTests : RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T T' v a ha d e hd he
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  obtain ⟨A, B, _, hB, ⟨f, hf⟩, hValue⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ (n + 1) T).1 v d hd a ha
  have hStandard : IsStandardAdditiveCharacter F ψ.complex⁻¹ := by
    rw [← complex_inverseCharacter]
    exact isStandardAdditiveCharacter_of_unitary _ (inverseCharacter_rational ψ hψ)
  obtain ⟨x', hx'⟩ := cuspidalWhittakerIdentityNonzero F (n + 1) T' ψ.complex⁻¹ hStandard
  let W' : G (n + 1) → ℂ := fun g =>
    cuspWhittaker F T' ψ.complex⁻¹ x' (realPlacePoint F (n + 1 + 1) v g * finitePoint F (n + 1 + 1) 1)
  have hW' : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' := ⟨x', 1, rfl⟩
  have hActual (p : realStandardKFinite (n + 1 + 1) d) : IsRealPlaceWhittaker F T ψ.complex v (B p) := by
    refine ⟨A p, 1, funext fun g => ?_⟩
    rw [hValue, mul_finitePoint_one]
  have hBbound (p : realStandardKFinite (n + 1 + 1) d) : HasGaugeBound (B p) :=
    hasGaugeBound_of_mem_model ((realPlaceUniformWhittakerModel F ψ hψ (n + 1) T v a ha d hd (B p)).1
      (hActual p))
  have hW'mem := (realPlaceUniformWhittakerModel F ψ hψ (n + 1) T' v a ha e he W').2 hW'
  have hW'reg := (realUniformWhittakerRegularity (n + 1) e (-a) W' hW'mem).1 []
  have hW'left : HasLeftCharacter (-a) W' := hW'reg.1
  have hW'continuous : Continuous W' := hW'reg.2.1.continuous
  have hW'bound : HasGaugeBound W' := hasGaugeBound_of_mem_model hW'mem
  by_contra hvan
  push Not at hvan
  let padPred := padGL (R := ℝ) (Nat.le_succ (n + 1))
  let V : G n → ℂ := fun g => W' (padPred g)
  have hVleft : HasLeftCharacter (-a) V := hasLeftCharacter_padGL (Nat.le_succ n) hW'left
  have hVcontinuous : Continuous V := hW'continuous.comp (UnequalAnalytic.continuous_padGL _)
  have hVbound : HasGaugeBound V := hasGaugeBound_padGL (Nat.le_succ n) hW'bound
  have hAdjacent (p : realStandardKFinite (n + 1 + 1) d) :=
    realEqualLastRowDescent n (realQuotientMeasureData n) (realQuotientMeasureData (n + 1))
      a (B p) W' (hB.1 p) hW'left (hB.2.1 p).continuous hW'continuous (hBbound p) hW'bound
      (fun Φ => hvan (B p) W' Φ (realQuotientMeasureData (n + 1)) (hActual p) hW')
  have hRankZero := descent_to_rankZero (Nat.lt_succ_self n) hB hBbound
    hVleft hVcontinuous hVbound hAdjacent
  let V₀ : G 0 → ℂ := fun g => W' (padGL (Nat.succ_le_succ hr.le) g)
  have hV₀left : HasLeftCharacter (-a) V₀ := hasLeftCharacter_padGL hr.le hW'left
  have hV₀continuous : Continuous V₀ := hW'continuous.comp (UnequalAnalytic.continuous_padGL _)
  have hV₀bound : HasGaugeBound V₀ := hasGaugeBound_padGL hr.le hW'bound
  let X := firstRootDirection hr
  let fX : realStandardKFinite (n + 1 + 1) d :=
    ⟨rightDerivative (matrixModel ℝ (n + 1 + 1)) X f,
      Langlands.Archimedean.rightDerivative_mem_kFiniteFunctions_realStandardModule _ _ f.2 X⟩
  have hBX : B fX = rightDerivative (matrixModel ℝ (n + 1 + 1)) X (B f) := hB.2.2.2.2 X f fX rfl
  obtain ⟨σ, hInt⟩ := exists_integrable hr (realQuotientMeasureData 0) (hB.1 f) hV₀left
    (hB.2.1 f).continuous hV₀continuous (hBbound f) hV₀bound
  obtain ⟨τ, hIntX⟩ := exists_integrable hr (realQuotientMeasureData 0) (hB.1 fX) hV₀left
    (hB.2.1 fX).continuous hV₀continuous (hBbound fX) hV₀bound
  have hZero (p : realStandardKFinite (n + 1 + 1) d) : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      realUnequalIntegral hr (realQuotientMeasureData 0) (B p) V₀ s = 0 := by
    simpa only [V, V₀, padPred, UnequalAnalytic.padGL_padGL] using hRankZero p
  obtain ⟨σ', hVan⟩ := hZero f
  obtain ⟨τ', hVanX⟩ := hZero fX
  rw [hBX] at hIntX hVanX
  have hProduct := value_eq_zero_of_integrals_eq_zero hr (realQuotientMeasureData 0)
    (hB.2.1 f) (hB.1 f) hV₀continuous (σ₀ := max σ τ)
    (fun s hs => hInt s ((le_max_left _ _).trans_lt hs))
    (fun s hs => hIntX s ((le_max_right _ _).trans_lt hs)) hVan hVanX
  have hV₀one : V₀ 1 = cuspWhittaker F T' ψ.complex⁻¹ x' 1 := by
    change cuspWhittaker F T' ψ.complex⁻¹ x'
      (realPlacePoint F (n + 1 + 1) v (padGL _ 1) * finitePoint F (n + 1 + 1) 1) = _
    rw [map_one, mul_finitePoint_one, realPlacePoint_one]
  exact hx' (by simpa only [hf, hV₀one, one_mul] using hProduct)

end Langlands.Global.RankinSelbergGlobal
