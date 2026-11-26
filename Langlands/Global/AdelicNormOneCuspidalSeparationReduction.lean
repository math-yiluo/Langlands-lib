import Langlands.Global.AdelicNormOneClassicalCuspidalDensityStatement
import Langlands.Global.AdelicNormOneCuspidalRapidDecay
import Langlands.Global.AdelicModerateCuspidalSmoothing
import Langlands.Global.AdelicTestKernelNonvanishing
import Langlands.Global.AdelicNormOneHaarRightInvariantProof
import Langlands.Analysis.Local.QuotientMass

/-! # Norm-one cuspidal separation from classical approximation -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj ENNReal InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RepresentationGrowth InfiniteAdelicGroupPoints

/-- Classical approximation on the norm-one quotient suffices for separation
of the continuous moderate cuspidal input. -/
def NormOneCuspidalSeparationReductionStatement : Prop :=
  AdelicNormOneClassicalCuspidalDensityStatement.{u} → NormOneCuspidalSeparationStatement.{u}

theorem normOneCuspidalSeparation_of_classicalDensity : NormOneCuspidalSeparationReductionStatement.{u} := by
  intro hDensity F _ _ G _ _ hG d N hsmooth Kinf rho hK hN hrho f hfInv hf hGrow hCusp hOrth
  let := normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  let A := AdelicGroupPoints F G
  let Q := NormOneRationalQuotient F G
  let ν := normOneRationalQuotientHaarMeasure F G
  let : ν.IsOpenPosMeasure := (normOneRationalQuotientHaarMeasure_isCompatible F G).isOpenPosMeasure
  let H := adelicHeight F G rho
  by_contra hnonzero
  obtain ⟨h, hh, hf₁⟩ := adelicTestKernelNonvanishing hsmooth f hf hnonzero
  let g : A → ℂ := rightConvolution F G h f
  obtain ⟨hg, hgInv, hgCusp, hgGrowth⟩ :=
    adelicModerateCuspidalSmoothing hsmooth rho hN h f hh hf hfInv hGrow hCusp
  obtain ⟨S, _, hS, hDecay⟩ := adelicNormOneCuspidalRapidDecay hsmooth rho hG hN
  have hRapid (v : A → ℂ) (hv : IsAdelicSmoothFunction F G v)
      (hInv : IsLeftInvariantUnder F G (rationalSubgroup F G) v)
      (hCus : HasZeroProperParabolicConstantTerms v) (hGr : HasUniformDirectionalHeightGrowth hsmooth rho v) :
      ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ‖v x‖ * H x ^ m ≤ C := by
    obtain ⟨R, hR, hGr⟩ := hGr
    exact hDecay v hv hInv hCus R hR hGr
  have hMem {v : A → ℂ} (hv : Continuous v)
      (hInv : IsLeftInvariantUnder F G (rationalSubgroup F G) v)
      (hDec : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ‖v x‖ * H x ^ m ≤ C) :
      MemLp (normOneRationalRestriction v) 2 ν := by
    obtain ⟨C, _, hC⟩ := hDec 0
    exact memLp_normOneRationalRestriction hG hS hv hInv
      (fun x hx => by simpa only [pow_zero, mul_one] using hC x hx) 2
  have hgMem := hMem hg.1 hgInv (hRapid g hg hgInv hgCusp hgGrowth)
  let v := hgMem.toLp (normOneRationalRestriction g)
  have hzero : v = 0 := by
    by_contra hne
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hne
    obtain ⟨ψ, hψ, hψCusp, hψGrowth, hClose⟩ := hDensity F G hG hsmooth Kinf rho hK hN hrho
      g hgInv hg hgCusp hgGrowth (ENNReal.ofReal ‖v‖) (ENNReal.ofReal_pos.mpr hvpos)
    have hψDecay := hRapid ψ hψ.2.1 hψ.1 hψCusp hψGrowth
    have hψMem := hMem hψ.2.1.1 hψ.1 hψDecay
    let w := hψMem.toLp (normOneRationalRestriction ψ)
    obtain ⟨_, hPair⟩ := adelicNormOneCuspidalPairing_rightConvolution rho hG hN S hS
      f ψ h hf hψ.2.1.1 hh.1.1 hh.2.1 hfInv hψ.1 hGrow hψDecay
    have hPair₀ : (∫ x, normOneCuspidalPairingIntegrand g ψ 1 x ∂ν) = 0 := by
      rw [hPair]
      simp only [fun a => (hOrth ψ hψ hψCusp a).2, mul_zero, integral_zero]
    have hInner : inner ℂ w v = 0 := by
      rw [L2.inner_def]
      refine (integral_congr_ae ?_).trans hPair₀
      filter_upwards [hgMem.coeFn_toLp, hψMem.coeFn_toLp] with x hx hy
      change v x = normOneRationalRestriction g x at hx
      change w x = normOneRationalRestriction ψ x at hy
      rw [RCLike.inner_apply, hx, hy]
      simp only [normOneCuspidalPairingIntegrand, normOneRationalRestriction, mul_one]
    have hwv : ‖v - w‖ < ‖v‖ := by
      change ‖hgMem.toLp _ - hψMem.toLp _‖ < _
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      simpa using (ENNReal.toReal_lt_toReal hClose.ne_top ENNReal.ofReal_ne_top).mpr hClose
    have hi := norm_inner_le_norm (𝕜 := ℂ) (v - w) v
    rw [inner_sub_left, hInner, sub_zero, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hi
    exact (not_lt_of_ge hi) (by simpa only [pow_two] using mul_lt_mul_of_pos_right hwv hvpos)
  have hAE : normOneRationalRestriction g =ᵐ[ν] (0 : Q → ℂ) := by
    have hvAE : (v : Q → ℂ) =ᵐ[ν] normOneRationalRestriction g := hgMem.coeFn_toLp
    rw [hzero] at hvAE
    exact hvAE.symm.trans (Lp.coeFn_zero ℂ 2 ν)
  have hgZero := Measure.eq_of_ae_eq hAE (continuous_normOneRationalRestriction hg.1 hgInv) continuous_const
  have hone := congrFun hgZero (LeftCosetSpace.mk (rationalNormOneSubgroup F G) 1)
  rw [normOneRationalRestriction_mk hgInv] at hone
  exact hf₁ hone

end Langlands.Global
