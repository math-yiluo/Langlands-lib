import Langlands.Global.AdelicNormOneKernelVector
import Langlands.Global.AdelicQuotientConvolutionGrowth

/-! # Polynomial bounds on norm-one partial convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F H
local notation "A₁" => normOneSubgroup F H
local notation "Γ" => positiveRationalSubgroup F H T i
local notation "dq" => positiveRationalQuotientHaarMeasure F H T i
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F H T i hi I e hc
local notation "dg" => (Measure.haar : Measure A)
local notation "νP" => normalizedPositiveHaarMeasure F H T i hi I e hc
local notation "V" => Lp ℂ 2 dq

include hi e hc in
/-- Norm-one partial convolution has a polynomial bound in its evaluation point, uniformly for
kernels supported in a fixed compact set and bounded by a common constant. -/
theorem exists_normOnePartialConvolution_bound {N : ℕ}
    (rho : MatrixRepresentation H (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (D : Set A) (hD : IsCompact D) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ (K : C_c(A, ℂ)), tsupport K ⊆ D → (∀ z, ‖K z‖ ≤ M) →
      ∀ (x : A₁) (v : V), ‖normOnePartialConvolution T i K v (x : A)‖ ≤
        C * adelicHeight F H rho (x : A) ^ d * ‖v‖ := by
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F H T i hi I e hc
  obtain ⟨ρ, hρ⟩ := exists_positiveBump T i hi I e hc
  obtain ⟨Mρ, hMρ⟩ := ρ.continuous.bounded_above_of_compact_support ρ.hasCompactSupport
  let D₁ : Set A₁ := {n | (n : A)⁻¹ ∈ D}
  have hD₁ : IsCompact D₁ := ((Homeomorph.inv A).isClosedEmbedding.comp
    (isClosed_normOneSubgroup F H).isClosedEmbedding_subtypeVal).isCompact_preimage hD
  let E := normOneDecomposition F H T i hi I e
  let S : Set A := E '' (tsupport ρ ×ˢ D₁)
  have hS : IsCompact S := (ρ.hasCompactSupport.prod hD₁).image E.continuous
  obtain ⟨d, hMass⟩ := adelicPositiveRationalConjugateGrowth_allPoints rho T i hi I e hc hN hrho
  obtain ⟨B, hB, hMass⟩ := hMass (S * S⁻¹) (hS.mul hS.inv)
  let U : ℝ := max Mρ 0 * M
  have hU : 0 ≤ U := mul_nonneg (le_max_right _ _) hM
  let C := ‖(∫ b, ρ b ∂νP)⁻¹‖ * U * Real.sqrt ((dg).real S * B)
  refine ⟨C, mul_nonneg (mul_nonneg (norm_nonneg _) hU) (Real.sqrt_nonneg _), d,
    fun K hK hKM x v => ?_⟩
  let f : C_c(A, ℂ) := normOneSmoothingKernel T i hi I e K ρ
  have hfS : ∀ a, a ∉ S → f a = 0 := by
    intro a ha
    let b := positiveFactor F H T i hi I e a
    let n := normOneFactor F H T i hi I e a
    change ρ b * starRingEnd ℂ (K ((n : A)⁻¹)) = 0
    by_cases hb : b ∈ tsupport ρ
    · by_cases hn : (n : A)⁻¹ ∈ tsupport K
      · exact absurd ⟨(b, n), ⟨hb, hK hn⟩, positivePointMap_mul_normOneFactor F H T i hi I e a⟩ ha
      · rw [image_eq_zero_of_notMem_tsupport hn, map_zero, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hb, zero_mul]
  have htf : tsupport f ⊆ S := closure_minimal (fun a ha => by_contra fun h => ha (hfS a h)) hS.isClosed
  have hfU (a : A) : ‖f a‖ ≤ U := by
    change ‖ρ _ * starRingEnd ℂ (K _)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hMρ _).trans (le_max_left _ _)) (hKM _) (norm_nonneg _) (le_max_right _ _)
  have hind : Integrable (S.indicator fun _ => U) dg :=
    (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
  have hint : ∫ a, ‖f a‖ ∂dg ≤ U * (dg).real S := by
    calc
      _ ≤ ∫ a, S.indicator (fun _ => U) a ∂dg := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hind
          (Filter.Eventually.of_forall fun a => ?_)
        change ‖f a‖ ≤ S.indicator (fun _ => U) a
        by_cases ha : a ∈ S
        · rw [indicator_of_mem ha]; exact hfU a
        · rw [indicator_of_notMem ha, hfS a ha, norm_zero]
      _ = _ := by rw [integral_indicator_const _ hS.measurableSet, smul_eq_mul, mul_comm]
  obtain ⟨w, -, hw, hwb⟩ := Langlands.QuotientIntegration.quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F H T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F H T i hi I e hc) f
  let j : A → A := fun s => (x : A) * s * (x : A)⁻¹
  have hj : Continuous j := (continuous_const.mul continuous_id).mul continuous_const
  have hSj : IsCompact (Subtype.val ⁻¹' (j '' (S * S⁻¹)) : Set Γ) :=
    (isClosed_positiveRationalSubgroup F H T i hi I e hc).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((hS.mul hS.inv).image hj)
  have hmass : (dΓ).real (Subtype.val ⁻¹' (j '' (tsupport f * (tsupport f)⁻¹))) ≤
      B * adelicHeight F H rho (x : A) ^ d :=
    (measureReal_mono (preimage_mono (image_mono (Set.mul_subset_mul htf (Set.inv_subset_inv.mpr htf))))
      hSj.measure_lt_top.ne).trans (hMass x)
  let Hx := adelicHeight F H rho (x : A) ^ d
  have hHx : 1 ≤ Hx := one_le_pow₀ (one_le_adelicHeight F H rho hN x)
  have hsq : ‖w x‖ ^ 2 ≤ (U * Real.sqrt ((dg).real S * B) * Hx) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg measureReal_nonneg hB)]
    calc
      ‖w x‖ ^ 2 ≤ U * (∫ a, ‖f a‖ ∂dg) * (dΓ).real (Subtype.val ⁻¹'
          (j '' (tsupport f * (tsupport f)⁻¹))) := hwb x U hfU
      _ ≤ U * (U * (dg).real S) * (B * Hx) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hint hU) hmass measureReal_nonneg
          (mul_nonneg hU (mul_nonneg hU measureReal_nonneg))
      _ = U ^ 2 * ((dg).real S * B) * Hx := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_self_pow₀ hHx (by decide))
        (mul_nonneg (sq_nonneg _) (mul_nonneg measureReal_nonneg hB))
  have hwb' := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hU (Real.sqrt_nonneg _))
    (zero_le_one.trans hHx))).mp hsq
  have heq : normOnePartialConvolution T i K v (x : A) =
      (∫ b, ρ b ∂νP)⁻¹ * inner ℂ (w x) v := by
    rw [eq_inv_mul_iff_mul_eq₀ hρ, (hw x v).2]
    exact (positiveQuotientLpSmoothing_normOneSmoothingKernel T i hi I e hc K ρ v x).symm
  rw [heq, norm_mul]
  calc
    _ ≤ ‖(∫ b, ρ b ∂νP)⁻¹‖ * (‖w x‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm (w x) v) (norm_nonneg _)
    _ ≤ ‖(∫ b, ρ b ∂νP)⁻¹‖ * (U * Real.sqrt ((dg).real S * B) * Hx * ‖v‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwb' (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by dsimp only [C, Hx]; ring

end Langlands.Global
