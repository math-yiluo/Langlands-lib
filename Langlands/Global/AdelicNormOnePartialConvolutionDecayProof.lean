import Langlands.Automorphic.GroupSchemeNormOnePartialConvolution
import Langlands.Global.AdelicDixmierMalliavin
import Langlands.Global.AdelicNormOneCuspidalFamilyTranslateDecay
import Langlands.Global.AdelicNormOnePartialConvolutionDecayStatement
import Langlands.Global.AdelicTestConvolution

/-! # Uniform rapid decay of norm-one partial convolutions -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField
open scoped CategoryTheory.MonObj CompactlySupported ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints RepresentationGrowth

section TestKernels

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] {d : ℕ}

local notation "A" => AdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure A)

omit [LocallyOfFiniteType G.X.hom] in
private theorem isAdelicTestFunction_conj (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {f : A → ℂ} (hf : IsAdelicTestFunction F G f) :
    IsAdelicTestFunction F G (fun x => starRingEnd ℂ (f x)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨L, hLo, hL⟩ := hf.1.2.2
  obtain ⟨U, hUo, hU⟩ := hf.2.2
  refine ⟨⟨Complex.continuous_conj.comp hf.1.1, ?_, L, hLo, ?_⟩,
    hf.2.1.comp_left (map_zero _), U, hUo, ?_⟩
  · intro b
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).2
    exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff (n := ∞)).contMDiff.comp
      ((isPlotSmooth_iff_contMDiff F G hsmooth _).1 (hf.1.2.1 b))
  · exact fun l hl x => congrArg (starRingEnd ℂ) (hL l hl x)
  · exact fun l hl x => congrArg (starRingEnd ℂ) (hU l hl x)

private theorem isAdelicTestFunction_rightConvolution
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {k φ : A → ℂ}
    (hk : IsAdelicTestFunction F G k) (hφ : IsAdelicTestFunction F G φ) :
    IsAdelicTestFunction F G (rightConvolution F G k φ) := by
  have heq : Hecke.convolutionIntegral dg φ (fun a => k a⁻¹) = rightConvolution F G k φ := by
    rw [convolutionIntegral_eq_rightConvolution]
    simp only [inv_inv]
  exact heq ▸ isAdelicTestFunction_convolutionIntegral hsmooth hφ
    (isAdelicTestFunction_comp_inv hsmooth hk)

end TestKernels

set_option maxHeartbeats 800000 in
/-- Rapid decay of the norm-one partial convolution of a cuspidal `L²` class, with a uniform
bound on compact right translates of common norm-one representatives. -/
theorem normOnePartialConvolutionRapidDecay : NormOnePartialConvolutionRapidDecayStatement.{u} := by
  classical
  intro F _ _ G _ _ _ hG T i hi _ I _ e hc _ N rho hN hrho K hK B hB m
  let d := hG.smoothDimension
  have hsmooth : SmoothOfRelativeDimension d G.X.hom := hG.smoothDimension_spec
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let S := fullAEL2CuspidalSubmodule F G parabolicDynamic hG T i hi I e hc
  let K' : AdelicGroupPoints F G → ℂ := fun y => starRingEnd ℂ (K y)
  obtain ⟨n, φ, ψ, hTest, hSum⟩ :=
    (isAdelicTestFunction_conj hsmooth hK : IsAdelicTestFunction F G K').exists_eq_sum_convolution hG
  let κ (j : Fin n) :=
    Hecke.convolutionIntegral (Measure.haar : Measure (AdelicGroupPoints F G)) (φ j) (ψ j)
  let invKernel (j : Fin n) : AdelicGroupPoints F G → ℂ := fun a => ψ j a⁻¹
  have hκ (j : Fin n) : IsAdelicTestFunction F G (κ j) :=
    isAdelicTestFunction_convolutionIntegral hsmooth (hTest j).1 (hTest j).2
  have hInvKernel (j : Fin n) : IsAdelicTestFunction F G (invKernel j) :=
    isAdelicTestFunction_comp_inv hsmooth (hTest j).2
  let f (j : Fin n) (v : S) := normOnePartialConvolution T i (κ j) v.val
  let g (j : Fin n) (v : S) := normOnePartialConvolution T i (φ j) v.val
  have hg (j : Fin n) (v : S) : Continuous (g j v) :=
    continuous_normOnePartialConvolution T i hi I e hc (hTest j).1.1.1 (hTest j).1.2.1 v.val
  have hConv (j : Fin n) (v : S) : f j v = rightConvolution F G (invKernel j) (g j v) := by
    change normOnePartialConvolution T i
      (Hecke.convolutionIntegral Measure.haar (φ j) (ψ j)) v.val = _
    rw [convolutionIntegral_eq_rightConvolution]
    exact normOnePartialConvolution_rightConvolution T i hi I e hc
      (hInvKernel j).1.1 (hInvKernel j).2.1 (hTest j).1.1.1 (hTest j).1.2.1 v.val
  have hSmooth (j : Fin n) (v : S) : IsAdelicSmoothFunction F G (f j v) := by
    rw [hConv]
    exact (adelicRightConvolutionDifferentiation F G d hsmooth _ _ (hInvKernel j)
      (hg j v).measurable (hg j v).locallyIntegrable).2.1
  have hWord (j : Fin n) (w : List (smoothModel F d)) :
      ∃ k : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G k ∧
        ∀ v : S, adelicIteratedDirectionalValue hsmooth w (f j v) = rightConvolution F G k (g j v) := by
    induction w with
    | nil =>
      exact ⟨invKernel j, hInvKernel j, fun v =>
        (adelicIteratedDirectionalValue_nil hsmooth _).trans (hConv j v)⟩
    | cons X w ih =>
      obtain ⟨k, hk, heq⟩ := ih
      refine ⟨_, (rightConvolutionKernelDerivative_isTestFunction hsmooth X hk).1, fun v => ?_⟩
      rw [adelicIteratedDirectionalValue_cons, heq v]
      funext x
      rw [← pair_projections F G x, adelicDirectionalValue_pair]
      exact (adelicRightConvolutionDifferentiation F G d hsmooth k _ hk
        (hg j v).measurable (hg j v).locallyIntegrable).2.2 X _ _
  obtain ⟨R, hGrowth⟩ := exists_normOnePartialConvolution_growth T i hi I e hc rho hN hrho
  have hDer (j : Fin n) (w : List (smoothModel F d)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : S) x, ‖adelicIteratedDirectionalValue hsmooth w (f j v) x‖ ≤
        C * adelicHeight F G rho x ^ (R : ℝ) * ‖v.val‖ := by
    obtain ⟨k, hk, heq⟩ := hWord j w
    have hkφ := isAdelicTestFunction_rightConvolution hsmooth hk (hTest j).1
    obtain ⟨C, hC, hBound⟩ := hGrowth _ hkφ.1.1 hkφ.2.1
    refine ⟨C, hC, fun v x => ?_⟩
    rw [heq v, ← normOnePartialConvolution_rightConvolution T i hi I e hc
      hk.1.1 hk.2.1 (hTest j).1.1.1 (hTest j).1.2.1 v.val, Real.rpow_natCast]
    exact hBound v.val x
  obtain ⟨D, _, hCover, hDecay⟩ := adelicNormOneCuspidalFamilyTranslateDecay rho hsmooth hG hN
  have hEach (j : Fin n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : S) x, x ∈ D → ∀ b ∈ B,
      ‖f j v (x * b)‖ * adelicHeight F G rho x ^ m ≤ C * ‖v.val‖ := by
    obtain ⟨L, hLo, hL⟩ := (hκ j).1.2.2
    exact hDecay B hB ⟨L, hLo⟩ S (f j) (fun v => ‖v.val‖) (fun _ => norm_nonneg _)
      (fun v => (hSmooth j v).1)
      (fun v b => (isPlotSmooth_iff_contMDiff F G hsmooth _).1 ((hSmooth j v).2.1 b))
      (fun v => normOnePartialConvolution_isLeftInvariant T i (κ j) v.val)
      (fun v l hl x => normOnePartialConvolution_mul_right T i (hL l hl) v.val x)
      (fun v => normOnePartialConvolution_hasZeroProperParabolicConstantTerms T i hi I e hc
        parabolicDynamic hG (hκ j).1.1 (hκ j).2.1 v.property)
      (R : ℝ) (Nat.cast_nonneg _) (hDer j) m
  choose C hC hBound using hEach
  have hK' : K' = fun a => ∑ j, κ j a := funext hSum
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun x => ?_⟩
  obtain ⟨q, hq⟩ := hCover x
  refine ⟨q, fun v hv b hb => ?_⟩
  let y := rational F G q * x.val
  change ‖normOnePartialConvolution T i K' v (y * b)‖ * adelicHeight F G rho y ^ m ≤ _
  rw [hK', normOnePartialConvolution_sum T i hi I e hc Finset.univ κ
    (fun j _ => (hκ j).1.1) (fun j _ => (hκ j).2.1)]
  calc
    _ ≤ (∑ j, ‖f j ⟨v, hv⟩ (y * b)‖) * adelicHeight F G rho y ^ m :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg
        (zero_le_one.trans (one_le_adelicHeight F G rho hN y)) _)
    _ = ∑ j, ‖f j ⟨v, hv⟩ (y * b)‖ * adelicHeight F G rho y ^ m := Finset.sum_mul ..
    _ ≤ ∑ j, C j * ‖v‖ := Finset.sum_le_sum fun j _ => hBound j ⟨v, hv⟩ y hq b hb
    _ = _ := (Finset.sum_mul ..).symm

end Langlands.Global
