import Langlands.Analysis.IntegrableLinearKernelContinuity
import Langlands.Global.RankinSelberg.ArchimedeanMellinPairPowerGrowth
import Langlands.Global.RankinSelberg.ArchimedeanPairIdentityStripGrowth
import Langlands.Global.RankinSelberg.RealPairStripReflection
import Langlands.Global.RankinSelberg.RealWeightedKernelReflection

/-! # Extension of real normalized Mellin reflection from dense generators -/

noncomputable section

open MeasureTheory Set
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

namespace Langlands.Global.RankinSelbergGlobal.RealDenseMellinReflection

open Langlands.Analysis Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair ArchimedeanInverseMellin RealWeightedKernelReflection
open ArchimedeanRealPairIdentity (stripGrowth_of_stripExpType)
open RealJacquet (HasRealPairNormalizedGrowth)

variable {X Y V : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- The ordinary determinant Mellin integral of a continuous linear scalar kernel. -/
def kernelIntegral (μ : Measure X) (K : X → V →L[ℂ] ℂ) (δ : X → ℝ) (v : V) (s : ℂ) : ℂ :=
  ∫ x, K x v * (δ x : ℂ) ^ s ∂μ

private theorem kernelIntegrable_of_moment (μ : Measure X) (K : X → V →L[ℂ] ℂ) (δ : X → ℝ)
    (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x) (v : V)
    (hK : AEStronglyMeasurable (fun x => K x v) μ) (s : ℂ)
    (hI : Integrable (fun x => ‖K x v‖ * δ x ^ s.re) μ) :
    Integrable (fun x => K x v * (δ x : ℂ) ^ s) μ := by
  have hM : AEStronglyMeasurable (fun x => (δ x : ℂ) ^ s) μ :=
    ((Complex.measurable_ofReal.comp hδm).pow_const s).aestronglyMeasurable
  refine hI.mono' (hK.mul hM) (ae_of_all _ fun x => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x)]

private theorem exists_thetaCLM [IsTopologicalAddGroup V] [SequentialSpace V] [BarrelledSpace ℂ V]
    (μ : Measure X) (K : X → V →L[ℂ] ℂ) (δ : X → ℝ)
    (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x) (h : ℝ → ℂ) (hh : Measurable h) (hdec : RapidDecay h)
    (N : ℝ) (hK : ∀ v, AEStronglyMeasurable (fun x => K x v) μ)
    (hI : ∀ v, Integrable (fun x => ‖K x v‖ * δ x ^ N) μ) {a : ℝ} (ha : 0 < a) :
    ∃ T : V →L[ℂ] ℂ, ∀ v, T v = theta μ (fun x => K x v) δ h a := by
  obtain ⟨C, hC⟩ := hdec N
  let W (x : X) := h (a * δ x) • K x
  have hW (v : V) : Integrable (fun x => W x v) μ := by
    have hM : Measurable (fun x => h (a * δ x)) := hh.comp (measurable_const.mul hδm)
    refine ((hI v).const_mul (C * a ^ N)).mono'
      (show AEStronglyMeasurable (fun x => h (a * δ x) * K x v) μ from
        hM.aestronglyMeasurable.mul (hK v)) (ae_of_all _ fun x => ?_)
    simp only [W, smul_apply, smul_eq_mul, norm_mul]
    have hb := hC (a * δ x) (mul_pos ha (hδ x))
    rw [Real.mul_rpow ha.le (hδ x).le] at hb
    calc
      _ ≤ (C * (a ^ N * δ x ^ N)) * ‖K x v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨_, T, hT⟩ := integrableLinearKernelContinuity μ W hW
  refine ⟨T, fun v => ?_⟩
  rw [hT v]
  simp only [W, theta, smul_apply, smul_eq_mul, mul_comm]

/-- Continuous linear determinant Mellin kernels on a sequential barrelled space satisfy real normalized
reflection on the full space if they satisfy it on a set whose complex span is dense. -/
def RealDenseMellinReflectionStatement (V : Type*) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] : Prop :=
  ∀ [IsTopologicalAddGroup V] [SequentialSpace V] [BarrelledSpace ℂ V]
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : X → V →L[ℂ] ℂ) (Kd : Y → V →L[ℂ] ℂ) (δ : X → ℝ) (δd : Y → ℝ),
    Measurable δ → Measurable δd → (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    (∀ v, AEStronglyMeasurable (fun x => K x v) μ) →
    (∀ v, AEStronglyMeasurable (fun y => Kd y v) ν) →
    (∃ N : ℝ, ∀ σ : ℝ, N ≤ σ → ∀ v,
      Integrable (fun x => ‖K x v‖ * δ x ^ σ) μ ∧ Integrable (fun y => ‖Kd y v‖ * δd y ^ σ) ν) →
    ∀ (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ), sign ≠ 0 →
    ∀ S : Set V, Dense (Submodule.span ℂ S : Set V) →
      (∀ v ∈ S, HasRealPairNormalizedGrowth ds es dds ees b c hc sign
        (kernelIntegral μ K δ v) (kernelIntegral ν Kd δd v)) →
      ∀ v, HasRealPairNormalizedGrowth ds es dds ees b c hc sign
        (kernelIntegral μ K δ v) (kernelIntegral ν Kd δd v)

theorem realDenseMellinReflection : RealDenseMellinReflectionStatement V := by
  intro _ _ _ X Y _ _ μ ν _ _ K Kd δ δd hδm hδdm hδ hδd hK hKd ⟨N, hI⟩ ds es dds ees b c hc sign hsign S hDense hS
  let F := ordinaryWeight ds es b c hc sign 1 0
  let G := reflectedWeight dds ees 1 0
  let L := realPairLFactor ds es
  let Ld := realPairLFactor dds ees
  let E := pairReflectionFactor ds es b c hc sign
  obtain ⟨hF, hG, hFdec, hGdec, hFM, hGM⟩ := realWeights_data ds es dds ees b c hc sign
    (rate := 1) one_pos 0
  have hE : Differentiable ℂ E := differentiable_pairReflectionFactor ds es b c hc sign
  have hEnz (s : ℂ) : E s ≠ 0 := mul_ne_zero hsign (Units.ne_zero _)
  have hEnorm (s : ℂ) : ‖E s‖ = ‖E (s.re : ℂ)‖ := by
    dsimp only [E, pairReflectionFactor, realPairEpsilon]
    rw [norm_mul, norm_mul,
      RealBlockParameters.norm_realEpsilon_eq_of_re_eq _ b c hc (Complex.ofReal_re s.re).symm]
  have thetaEq (a : ℝ) (ha : 0 < a) (v : V) :
      theta μ (fun x => K x v) δ F a = (a : ℂ) * theta ν (fun y => Kd y v) δd G a⁻¹ := by
    obtain ⟨A, hA⟩ := exists_thetaCLM μ K δ hδm hδ F hF hFdec N hK
      (fun v => (hI N le_rfl v).1) ha
    obtain ⟨B, hB⟩ := exists_thetaCLM ν Kd δd hδdm hδd G hG hGdec N hKd
      (fun v => (hI N le_rfl v).2) (inv_pos.mpr ha)
    let C : V →L[ℂ] ℂ := (a : ℂ) • B
    have hBase (w : V) (hw : w ∈ S) : A w = C w := by
      rw [hA w, show C w = (a : ℂ) * B w from rfl, hB w]
      have hReflect := realWeightedKernelReflection μ ν
        (fun s x => K x w * (δ x : ℂ) ^ s) (fun s y => Kd y w * (δd y : ℂ) ^ s)
        δ δd hδm hδdm hδ hδd
        (fun s x => by rw [Complex.cpow_zero, mul_one])
        (fun s y => by rw [Complex.cpow_zero, mul_one])
        ⟨N, fun s hs => ⟨kernelIntegrable_of_moment μ K δ hδm hδ w (hK w) s (hI s.re hs.le w).1,
          kernelIntegrable_of_moment ν Kd δd hδdm hδd w (hKd w) s (hI s.re hs.le w).2⟩⟩
        ds es dds ees b c hc sign (hS w hw) 1 0 one_pos ha
      simpa only [F, G, Complex.cpow_zero, mul_one] using hReflect
    have hSpan : Submodule.span ℂ S ≤ LinearMap.ker (A - C).toLinearMap :=
      Submodule.span_le.mpr fun w hw => LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hBase w hw))
    have hEq := congrFun (Continuous.ext_on hDense A.continuous C.continuous
      (fun w hw => sub_eq_zero.mp (LinearMap.mem_ker.mp (hSpan hw)))) v
    exact (hA v).symm.trans (hEq.trans (congrArg ((a : ℂ) * ·) (hB v)))
  have hFM' (s : ℂ) : (E s)⁻¹ * mellin F (-s) = Complex.exp (s ^ 2) * L.denominator s := by
    rw [show mellin F (-s) = L.denominator s * E s * gaussianFactor 1 0 s from hFM s]
    simp only [gaussianFactor, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero]
    rw [mul_comm (L.denominator s), ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (hEnz s), one_mul, mul_comm]
  have hGM' (s : ℂ) : mellin G (s - 1) = Complex.exp (s ^ 2) * Ld.denominator (1 - s) := by
    rw [show mellin G (s - 1) = Ld.denominator (1 - s) * gaussianFactor 1 0 s from hGM s, mul_comm]
    simp [gaussianFactor]
  intro v
  obtain ⟨R, hR, hRgrowth, hRight, hLeft⟩ := mellinPairEntireValue μ ν (fun x => K x v) δ
    (fun y => Kd y v) δd F G N L Ld (fun s => (E s)⁻¹) (hK v) (hKd v) hδm hδdm hδ hδd
    hF hG hFdec hGdec (fun σ hσ => (hI σ hσ v).1) (fun σ hσ => (hI σ hσ v).2)
    (fun a ha => thetaEq a ha v) hFM' hGM' (fun s => (hE s).inv (hEnz s))
    (fun s => by simp only [norm_inv, hEnorm s])
    (stripGrowth_realPairLFactor_denominator ds es) (stripGrowth_realPairLFactor_denominator dds ees)
  let Rd (s : ℂ) := E (1 - s) * R (1 - s)
  have hReflectDiff : Differentiable ℂ (fun s : ℂ => 1 - s) := differentiable_id.const_sub 1
  have hEgr := stripGrowth_of_stripExpType (stripExpType_pairReflectionFactor ds es b c hc sign).comp_one_sub
  refine ⟨R, Rd, hR, (hE.comp hReflectDiff).mul (hR.comp hReflectDiff), hRgrowth,
    hEgr.mul hRgrowth.comp_one_sub, ⟨N, fun s hs => ?_⟩, fun s => ?_⟩
  · refine ⟨(hRight s hs.le).trans (mul_comm _ _), ?_⟩
    have hRe : (1 - s).re ≤ 1 - N := by simp only [Complex.sub_re, Complex.one_re]; linarith
    change E (1 - s) * R (1 - s) = Ld.denominator s * kernelIntegral ν Kd δd v s
    rw [hLeft (1 - s) hRe, sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ (hEnz (1 - s)), one_mul]
    exact mul_comm _ _
  · change E (1 - (1 - s)) * R (1 - (1 - s)) = E s * R s
    rw [sub_sub_cancel]

end Langlands.Global.RankinSelbergGlobal.RealDenseMellinReflection
