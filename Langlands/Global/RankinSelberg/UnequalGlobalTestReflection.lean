import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnequalDualPartialNonvanishing
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Nonvanishing of the reflected partial integral for the same global vectors -/

noncomputable section

open NumberField Filter
open scoped Classical CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.UnequalDualPartial

open Langlands.Automorphic CompletionPadic CuspidalPairBoundaryNonvanishing
open CuspidalPairFunctionalEquation (HasSatakeBound residueCardinality)
open CuspidalPairEulerConvergence (two_le_residueCardinality norm_spectralPoint)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}

private theorem partialEulerFactor_ne_zero
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    {A B : ℝ} (hA : HasSatakeBound P A) (hB : HasSatakeBound P' B)
    {s : ℂ} (hs : A + B < s.re) (v : {v : FinitePlace F // v ∉ S}) :
    partialEulerFactor P P' hP hP' v s ≠ 0 := by
  let q : ℝ := residueCardinality v.1
  have hq : 1 < q := by
    dsimp only [q]
    have hv := two_le_residueCardinality v.1
    exact_mod_cast (show 1 < residueCardinality v.1 by omega)
  have hδ {α β : ℂˣ} (ha : ‖(α : ℂ)‖ ≤ q ^ A) (hb : ‖(β : ℂ)‖ ≤ q ^ B) :
      ‖(α : ℂ) * β * RankinSelberg.spectralPoint (residueCardinality v.1) s‖ < 1 := by
    rw [norm_mul, norm_mul, norm_spectralPoint]
    change ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * q ^ (-s.re) < 1
    calc
      _ ≤ q ^ A * q ^ B * q ^ (-s.re) := by gcongr
      _ = q ^ (A + B - s.re) := by rw [← Real.rpow_add (by linarith : 0 < q),
          ← Real.rpow_add (by linarith : 0 < q), sub_eq_add_neg]
      _ < q ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hq (sub_neg.mpr hs)
      _ = 1 := Real.rpow_zero _
  unfold partialEulerFactor
  obtain ⟨w, -, hw⟩ := CuspidalPairAbsoluteConvergence.exists_hasSum_pairLog
    (P.spectralSystem.eigenvalues v.1 fun hv => v.2 (hP hv))
    (P'.spectralSystem.eigenvalues v.1 fun hv => v.2 (hP' hv))
    (RankinSelberg.spectralPoint (residueCardinality v.1) s)
    (fun α hα β hβ => hδ (hA v.1 _ α hα) (hB v.1 _ β hβ))
  rw [hw]
  exact Complex.exp_ne_zero _

/-- Ordinary nonvanishing of the partial Whittaker integral implies nonvanishing of the
dual partial integral arbitrarily far to the right, for the same vectors. -/
theorem partialDualWhittakerIntegral_ne_zero_above_of_ordinary
    {h : t < r} (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ z : F, ψ (algebraMap F (Adeles F) z) = 1)
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    {x : T.Space} {x' : T'.Space} (hx : IsSphericalOutside F T S x)
    (hx' : IsSphericalOutside F T' S x')
    (hOrd : ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ partialUnequalWhittakerIntegral F h S
      (cuspWhittaker F T ψ.complex x) (cuspWhittaker F T' ψ.complex⁻¹ x') s ≠ 0) :
    ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ partialDualWhittakerIntegral F h S
      (Unfolding.dualWhittaker F h T ψ.complex x)
      (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s ≠ 0 := by
  let I := unequalIntegral F h ψ.complex (cuspFunction F T x) (cuspFunction F T' x')
  let Id := dualUnequalIntegral F h ψ.complex
    (dualFunction F (r + 1) (cuspFunction F T x))
    (dualFunction F (t + 1) (cuspFunction F T' x'))
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨C, -, hC⟩ := unequalUnfoldingStatement_proof F r t h T T'
  obtain ⟨hU, hUd⟩ := hC ψ.complex hstd x x'
  obtain ⟨-, -, hI, -, hFE⟩ :=
    UnequalAnalytic.unequalAnalyticStatement_proof F r t h T T' ψ.complex hstd x x'
  obtain ⟨σ, hσ⟩ := unequalEulerFactorization F ψ hψ r t h T T' P P' S hP hP' hS
  obtain ⟨A, hA⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨B, hB⟩ := exists_hasSatakeBound_presentation T' P'
  obtain ⟨z, hz, hz₀⟩ := hOrd (max C (max σ (A + B)))
  obtain ⟨-, hsum, p, hp, hprod⟩ := hσ x x' hx hx' z
    ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hz))
  have hbound : A + B < z.re := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hz)
  have hp₀ : p ≠ 0 := by
    let f v := partialEulerFactor P P' hP hP' v z
    have he : (fun v => 1 + (f v - 1)) = f := funext fun _ => by ring
    have hn := tprod_one_add_ne_zero_of_summable (f := fun v => f v - 1)
      (fun v => by rw [congrFun he v]; exact partialEulerFactor_ne_zero P P' hP hP' hA hB hbound v)
      hsum
    rwa [he, hp.tprod_eq] at hn
  have hIz : I z ≠ 0 := by
    change unequalIntegral F h ψ.complex (cuspFunction F T x) (cuspFunction F T' x') z ≠ 0
    rw [(hU z ((le_max_left _ _).trans_lt hz)).2, hprod]
    exact mul_ne_zero hz₀ hp₀
  let J (s : ℂ) : ℂ := I (1 - s)
  have hJ : Differentiable ℂ J :=
    hI.comp (show Differentiable ℂ (fun s : ℂ => 1 - s) by fun_prop)
  have hJ₀ : J (1 - z) ≠ 0 := by simpa only [J, sub_sub_cancel] using hIz
  have hJa : AnalyticOnNhd ℂ J Set.univ := fun s _ => hJ.analyticAt s
  have hJn : ∀ᶠ s in codiscrete ℂ, J s ≠ 0 := hJa.preimage_zero_mem_codiscrete hJ₀
  intro a
  let b := max a (1 + C)
  let s₀ : ℂ := ((b + 1 : ℝ) : ℂ)
  have hs₀ : b < s₀.re := by simp [s₀]
  have hright : ∀ᶠ s : ℂ in 𝓝[≠] s₀, b < s.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs₀)
  obtain ⟨s, hs, hsJ⟩ := (hright.and (hJn.filter_mono (nhdsNE_le_codiscrete s₀))).exists
  have hsD : (1 - s).re < -C := by
    have hh : 1 + C < s.re := (le_max_right _ _).trans_lt hs
    rw [Complex.sub_re, Complex.one_re]
    linarith
  obtain ⟨hint, hId⟩ := hUd (1 - s) hsD
  rw [sub_sub_cancel] at hint hId
  have hG := hFE (1 - s)
  rw [sub_sub_cancel] at hG
  refine ⟨s, (le_max_left _ _).trans_lt hs,
    partialDualWhittakerIntegral_ne_zero h ψ hψ P P' hP hP' hS hx hx' s hint.2.2 ?_⟩
  rwa [← hId, ← hG]

end Langlands.Global.RankinSelbergGlobal.UnequalDualPartial
