import Langlands.Global.RankinSelberg.ArchimedeanGaussianMellinPair
import Langlands.Global.RankinSelberg.ArchimedeanComplexPairFactor
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth

/-! # Weighted reflection for the complex pair factors -/

noncomputable section

open MeasureTheory Complex Set
open scoped NNReal

set_option autoImplicit false

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ComplexWeightedKernelReflection

open Langlands.LocalFactor.Archimedean
open ArchimedeanMellinPair (RapidDecay theta)
open ArchimedeanRealPairIdentity (norm_kernel kernel_zero_eq)
open ArchimedeanInverseMellin
open ArchimedeanComplexPairFactor (complexLFactor_stripExpType complexEpsilon_stripExpType)
open ComplexJacquet (HasComplexPairNormalizedGrowth)

/-- The reflection factor including the constant central sign. -/
def pairReflectionFactor (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ) (s : ℂ) : ℂ :=
  sign * (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)

theorem differentiable_pairReflectionFactor (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ) :
    Differentiable ℂ (pairReflectionFactor ds es a sign) :=
  (differentiable_complexEpsilon (complexPairBlocks ds es) a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero)).const_mul sign

theorem stripExpType_pairReflectionFactor (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ) :
    StripExpType (pairReflectionFactor ds es a sign) :=
  (StripExpType.const sign).mul
    (complexEpsilon_stripExpType (complexPairBlocks ds es) a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero))

/-- The explicit ordinary weight for a complex pair. -/
def ordinaryWeight (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ) (rate B : ℝ) : ℝ → ℂ :=
  mellinInv 0 (gaussianOrdinaryTransform (complexPairLFactor ds es).denominator
    (pairReflectionFactor ds es a sign) rate B)

/-- The explicit reflected weight for a complex pair. -/
def reflectedWeight (ds es : List ComplexCharacterData) (rate B : ℝ) : ℝ → ℂ :=
  mellinInv 0 (gaussianReflectedTransform
    (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator rate B)

theorem complexWeights_data (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ)
    {rate : ℝ} (hrate : 0 < rate) (B : ℝ) :
    let f := ordinaryWeight ds es a sign rate B
    let fd := reflectedWeight ds es rate B
    Measurable f ∧ Measurable fd ∧ RapidDecay f ∧ RapidDecay fd ∧
      (∀ s : ℂ, mellin f (-s) = (complexPairLFactor ds es).denominator s *
        pairReflectionFactor ds es a sign s * gaussianFactor rate B s) ∧
      (∀ s : ℂ, mellin fd (s - 1) = (complexPairLFactor (ds.map ComplexCharacterData.inv)
        (es.map ComplexCharacterData.inv)).denominator (1 - s) * gaussianFactor rate B s) :=
  archimedeanGaussianMellinPair _ _ _ _ _ hrate (complexPairLFactor ds es).entire
    (complexPairLFactor _ _).entire (differentiable_pairReflectionFactor ds es a sign)
    (complexLFactor_stripExpType _) (complexLFactor_stripExpType _) (stripExpType_pairReflectionFactor ds es a sign)

/-- Continuity extends the large-height exponential bounds to every point of a strip. -/
theorem stripExpType_of_hasStripExponentialGrowth {F : ℂ → ℂ} (hF : Continuous F)
    (h : HasStripExponentialGrowth F) : StripExpType F := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hbound⟩ := h a b
  let R := max T 0
  have hbox : IsCompact (Icc a b ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun p : ℝ × ℝ => F ((p.1 : ℂ) + p.2 * I)) := hF.comp (by fun_prop)
  obtain ⟨M, hM⟩ := hbox.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C M, K, hC.trans (le_max_left _ _), hK, fun x hx hx' y => ?_⟩
  by_cases hy : T ≤ |y|
  · have hb : ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (K * |y|) := by
      simpa using hbound ((x : ℂ) + y * I) (by simpa using hx) (by simpa using hx') (by simpa using hy)
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  · have hy' : |y| ≤ R := (le_of_not_ge hy).trans (le_max_left _ _)
    refine (hM (x, y) ⟨⟨hx, hx'⟩, abs_le.mp hy'⟩).trans ((le_max_right C M).trans ?_)
    exact le_mul_of_one_le_right (hC.trans (le_max_left _ _)) (Real.one_le_exp (mul_nonneg hK (abs_nonneg _)))

/-- The Gaussian determinant-weight identity for complex kernels given a normalized reflection with strip growth. -/
def ComplexWeightedKernelReflectionStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (K : ℂ → X → ℂ) (L : ℂ → Y → ℂ) (δ : X → ℝ) (η : Y → ℝ),
    Measurable δ → Measurable η → (∀ x, 0 < δ x) → (∀ y, 0 < η y) →
    (∀ s x, K s x = K 0 x * (δ x : ℂ) ^ s) → (∀ s y, L s y = L 0 y * (η y : ℂ) ^ s) →
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (K s) μ ∧ Integrable (L s) ν) →
    ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (sign : ℂ),
    HasComplexPairNormalizedGrowth ds es a sign (fun s => ∫ x, K s x ∂μ) (fun s => ∫ y, L s y ∂ν) →
    ∀ (rate B : ℝ), 0 < rate → ∀ {b : ℝ}, 0 < b →
      theta μ (K 0) δ (ordinaryWeight ds es a sign rate B) b =
        (b : ℂ) * theta ν (L 0) η (reflectedWeight ds es rate B) b⁻¹

set_option maxHeartbeats 650000 in
theorem complexWeightedKernelReflection : ComplexWeightedKernelReflectionStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ K L δ η hδ hη hδ₀ hη₀ hK hL hConv ds es a sign hNorm rate B hrate b hb
  obtain ⟨N, Nd, hN, _, hNt, _, ⟨τ, hR⟩, hFE⟩ := hNorm
  obtain ⟨σ₀, hI⟩ := hConv
  let σ := max (max σ₀ τ) 1 + 1
  have hσ₀ : σ₀ < σ := by
    dsimp only [σ]
    linarith [le_max_left σ₀ τ, le_max_left (max σ₀ τ) (1 : ℝ)]
  have hστ : τ < σ := by
    dsimp only [σ]
    linarith [le_max_right σ₀ τ, le_max_left (max σ₀ τ) (1 : ℝ)]
  have hσ : (1 : ℝ) / 2 ≤ σ := by dsimp only [σ]; linarith [le_max_right (max σ₀ τ) (1 : ℝ)]
  obtain ⟨hKσ, hLσ⟩ := hI (σ : ℂ) (by simpa using hσ₀)
  have hK₀ : AEStronglyMeasurable (K 0) μ := by
    have hm : Measurable (fun x => (δ x : ℂ) ^ (-(σ : ℂ))) := (measurable_ofReal.comp hδ).pow_const _
    exact (hKσ.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
      (ae_of_all _ fun x => (kernel_zero_eq hδ₀ hK σ x).symm)
  have hL₀ : AEStronglyMeasurable (L 0) ν := by
    have hm : Measurable (fun y => (η y : ℂ) ^ (-(σ : ℂ))) := (measurable_ofReal.comp hη).pow_const _
    exact (hLσ.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
      (ae_of_all _ fun y => (kernel_zero_eq hη₀ hL σ y).symm)
  let D := (complexPairLFactor ds es).denominator
  let Dd := (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
  let E := pairReflectionFactor ds es a sign
  let H := gaussianFactor rate B
  have hDt : StripExpType D := complexLFactor_stripExpType _
  have hDdt : StripExpType Dd := complexLFactor_stripExpType _
  have hE := differentiable_pairReflectionFactor ds es a sign
  have hEt := stripExpType_pairReflectionFactor ds es a sign
  have hNt' := stripExpType_of_hasStripExponentialGrowth hN.continuous hNt
  obtain ⟨hm, hmt⟩ := gaussianOrdinaryTransform_spec D E hrate B (complexPairLFactor ds es).entire hE hDt hEt
  obtain ⟨hmd, hmdt⟩ := gaussianReflectedTransform_spec Dd hrate B (complexPairLFactor _ _).entire hDdt
  refine theta_mellinInv_reflection μ ν hK₀ hL₀ hδ hη hδ₀ hη₀ hσ
    (hKσ.norm.congr (ae_of_all _ (norm_kernel hδ₀ hK σ)))
    (hLσ.norm.congr (ae_of_all _ (norm_kernel hη₀ hL σ)))
    (N := N) (Nd := Nd) (D := D) (Dd := Dd) (E := E) (H := H) ?_ ?_ hFE
    ((hN.mul hE).mul (differentiable_gaussianFactor rate B)) ?_ hm hmd hmt hmdt ?_ ?_ hb
  · intro s hs
    exact (hR s (hs ▸ hστ)).1.trans (congrArg (D s * ·) (integral_congr_ae (ae_of_all _ (hK s))))
  · intro s hs
    exact (hR s (hs ▸ hστ)).2.trans (congrArg (Dd s * ·) (integral_congr_ae (ae_of_all _ (hL s))))
  · exact (stripDecay_gaussianFactor_mul (hNt'.mul hEt) hrate B).congr fun s => mul_comm _ _
  · intro s
    simp [gaussianOrdinaryTransform, H]
  · intro s
    rw [gaussianReflectedTransform, show -(s - 1) = 1 - s by ring, show 1 + (s - 1) = s by ring]

end Langlands.Global.RankinSelbergGlobal.ComplexWeightedKernelReflection
