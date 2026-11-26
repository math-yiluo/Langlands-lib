import Langlands.Global.RankinSelberg.ArchimedeanThetaNormalizedGrowth
import Langlands.Global.RankinSelberg.RealWeightedKernelReflection

/-! # The real normalized pair with growth from its theta reflection -/

noncomputable section

open MeasureTheory Complex
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.RealThetaNormalizedGrowth

open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair (RapidDecay theta archimedeanThetaNormalizedGrowth)
open ArchimedeanInverseMellin
open ArchimedeanRealPairFactor (realLFactor_stripExpType)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealWeightedKernelReflection (pairReflectionFactor differentiable_pairReflectionFactor
  stripExpType_pairReflectionFactor)

private theorem stripExpType_inv_block_epsilon (x : RealBlock) (a : ℝˣ) (c : ℝ≥0) (hc : 0 < c) :
    StripExpType (fun s => (x.epsilon a c hc s : ℂ)⁻¹) := by
  have hr : 0 < |(a : ℝ)| := abs_pos.mpr a.ne_zero
  cases x with
  | character d =>
    have h := ((StripExpType.ofReal_cpow hr).comp_ofReal_mul (-1)).comp_add (-1)
    refine (((StripExpType.const ((c : ℂ) * (d.character a : ℂ))⁻¹).mul h).mul
      (StripExpType.const (Complex.I ^ d.parity.val)⁻¹)).congr fun s => ?_
    change _ = (d.epsilon a c hc s : ℂ)⁻¹
    rw [RealCharacterData.coe_epsilon]
    simp only [mul_inv, ← Complex.cpow_neg, ofReal_neg, ofReal_one, neg_mul, one_mul,
      sub_eq_add_neg]
  | induced d =>
    have h := ((StripExpType.ofReal_cpow hr).comp_ofReal_mul (-2)).comp_add (-1)
    refine (((StripExpType.const ((c : ℂ) ^ 2 *
      ((((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) * (d.character (realToComplex a) : ℂ)))⁻¹).mul h).mul
      (StripExpType.const (Complex.I ^ (d.weight.natAbs + 1))⁻¹)).congr fun s => ?_
    change _ = (d.realInducedEpsilon a c hc s : ℂ)⁻¹
    rw [ComplexCharacterData.coe_realInducedEpsilon]
    simp only [mul_inv, ← Complex.cpow_neg, ofReal_neg, ofReal_ofNat]
    congr 2
    ring_nf

private theorem stripExpType_inv_realEpsilon (xs : List RealBlock) (a : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) : StripExpType (fun s => (realEpsilon xs a c hc s : ℂ)⁻¹) := by
  induction xs with
  | nil => exact (StripExpType.const 1).congr (by simp [realEpsilon])
  | cons x xs ih =>
    exact ((stripExpType_inv_block_epsilon x a c hc).mul ih).congr fun s => by
      simp [realEpsilon, mul_comm]

/-- The inverse real reflection factor has strip exponential type. -/
theorem stripExpType_pairReflectionFactor_inv (ds es : List RealBlock) (b : ℝˣ) (c : ℝ≥0)
    (hc : 0 < c) (sign : ℂ) :
    StripExpType (fun s => (pairReflectionFactor ds es b c hc sign s)⁻¹) :=
  ((StripExpType.const sign⁻¹).mul
    (stripExpType_inv_realEpsilon (realPairBlocks ds es) b c hc)).congr
    fun s => (mul_inv sign (realPairEpsilon ds es b c hc s : ℂ)).symm

/-- A real theta reflection gives the normalized growth package for its two determinant
transforms. -/
def RealThetaNormalizedGrowthStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (Fd : Y → ℂ) (δ : X → ℝ) (δd : Y → ℝ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable Fd ν → Measurable δ → Measurable δd →
    (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    ∀ (σ : ℝ), (∀ x : ℝ, σ ≤ x → Integrable (fun p => ‖F p‖ * δ p ^ x) μ) →
    (∀ x : ℝ, σ ≤ x → Integrable (fun p => ‖Fd p‖ * δd p ^ x) ν) →
    ∀ (ds es dds ees : List RealBlock) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ), sign ≠ 0 →
    ∀ (f fd : ℝ → ℂ), Measurable f → Measurable fd → RapidDecay f → RapidDecay fd →
    (∀ s : ℂ, mellin f (-s) = (realPairLFactor ds es).denominator s *
      pairReflectionFactor ds es b c hc sign s * Complex.exp (s ^ 2)) →
    (∀ s : ℂ, mellin fd (s - 1) = (realPairLFactor dds ees).denominator (1 - s) *
      Complex.exp (s ^ 2)) →
    (∀ β : ℝ, 0 < β → theta μ F δ f β = (β : ℂ) * theta ν Fd δd fd β⁻¹) →
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign
      (fun s => ∫ p, F p * (δ p : ℂ) ^ s ∂μ) (fun s => ∫ p, Fd p * (δd p : ℂ) ^ s ∂ν)

theorem realThetaNormalizedGrowth : RealThetaNormalizedGrowthStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F Fd δ δd hF hFd hδm hδdm hδ hδd σ hI hId ds es dds ees b c hc sign
    hsign f fd hfm hfdm hf hfd hfmellin hfdmellin hθ
  let L := (realPairLFactor ds es).denominator
  let Ld := (realPairLFactor dds ees).denominator
  let E := pairReflectionFactor ds es b c hc sign
  have hE₀ (s : ℂ) : E s ≠ 0 := mul_ne_zero hsign (Units.ne_zero _)
  obtain ⟨N, Nd, hN, hNd, hNt, hNdt, hR, hFE⟩ :=
    archimedeanThetaNormalizedGrowth μ ν F Fd δ δd hF hFd hδm hδdm hδ hδd σ hI hId L Ld E
      (realLFactor_stripExpType _) (realLFactor_stripExpType _)
      (stripExpType_pairReflectionFactor ds es b c hc sign)
      (stripExpType_pairReflectionFactor_inv ds es b c hc sign)
      (differentiable_pairReflectionFactor ds es b c hc sign) hE₀
      f fd hfm hfdm hf hfd hfmellin hfdmellin hθ
  exact ⟨N, Nd, hN, hNd, hNt.hasStripExponentialGrowth, hNdt.hasStripExponentialGrowth,
    ⟨σ, fun s hs => hR s hs.le⟩, hFE⟩

/-- Only agreement on a right half-plane is needed to transfer the normalized growth package. -/
theorem normalizedGrowth_congr_right {ds es dds ees : List RealBlock} {b : ℝˣ} {c : ℝ≥0}
    {hc : 0 < c} {sign : ℂ} {I Id J Jd : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id)
    (hR : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → I s = J s ∧ Id s = Jd s) :
    HasRealPairNormalizedGrowth ds es dds ees b c hc sign J Jd := by
  obtain ⟨σ, hσ⟩ := hR
  exact h.congr (fun s hs => (hσ s hs).1) (fun s hs => (hσ s hs).2)

end Langlands.Global.RankinSelbergGlobal.RealThetaNormalizedGrowth
