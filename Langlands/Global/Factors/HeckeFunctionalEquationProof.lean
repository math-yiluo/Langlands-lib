import Langlands.Global.Hecke.HeckeClassMellin
import Langlands.Global.Factors.HeckeDualThetaMellin
import Langlands.Global.Factors.HeckeEpsilonProduct
import Langlands.Global.Factors.HeckeLocalData
import Langlands.Global.Factors.HeckeArchimedeanZeta
import Langlands.Global.Factors.HeckeFunctionalEquationStatement

/-!
# The global functional equation of Hecke L-functions
-/

noncomputable section

open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Module
open scoped nonZeroDivisors Classical
open Langlands.Global.HeckeDivisor Langlands.Global.HeckeTheta
open Langlands.Global.HeckeDivisorEulerProduct
open Langlands.LocalFactor.Archimedean Langlands.LocalFactor.PadicAbelian
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.Hecke Langlands.HarmonicAnalysis
open Langlands.Global.HeckeAssembly

namespace Langlands.Global

universe u

theorem heckeGlobalFunctionalEquation_proof : HeckeGlobalFunctionalEquationStatement.{u} := by
  intro K _ _ χ ψ _ hdiag
  refine ⟨localData χ ψ hdiag, ?_⟩
  intro ψf hf μ aR hR aC hC dR dR' hdR hdR' dC dC' hdC hdC' finiteL finiteEps infDen dualInfDen
    infEps
  -- the archimedean and finite inputs
  obtain ⟨E, E', σA, hEd, hE'd, hE0, hE'0, hZ, hZ', hEps⟩ :=
    exists_archimedeanZeta χ aR aC dR dR' hdR hdR' dC dC' hdC hdC'
  obtain ⟨σf, S, hz, hε, hfin⟩ :=
    exists_finiteMellin_common_halfPlane χ ψ hdiag ψf hf μ aR hR aC hC
  choose T hTχ hTl hTf hTg using fun C : ClassGroup (𝓞 K) =>
    exists_thetaData aR aC dR dC χ ψ hdiag ψf hf μ hR hC (classRepresentative C)
  obtain ⟨σM, hσM⟩ := (T 1).exists_re_gt
  have hratio_eq : ∀ C w, (T C).ratio w = (T 1).ratio w := fun C w => by
    rw [DyadicCone.ThetaData.ratio, DyadicCone.ThetaData.ratio, hTl, hTl]
  -- notation
  set w : ℂ := (Units.torsionOrder K : ℂ) with hw_def
  have hw : w ≠ 0 := Nat.cast_ne_zero.mpr (Units.torsionOrder_pos K).ne'
  set κc : ℂ := (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ)) : ℂ) *
    Hecke.mixedGaussianFTConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
      (fun v => (dR v).parity) (fun v => (dC v).weight) with hκc_def
  have hinfEps : ∀ s, infEps s ≠ 0 := fun s =>
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => Units.ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun v _ => Units.ne_zero _)
  have hκc : κc ≠ 0 := by
    intro h0
    have h := hEps 0
    rw [h0, zero_mul] at h
    exact mul_ne_zero (hinfEps 0) (hE0 0) h.symm
  have hεne : ∀ s, ∏ v ∈ S, finiteEpsilon χ ψf μ v s ≠ 0 := fun s =>
    Finset.prod_ne_zero_iff.mpr fun v _ => finiteEpsilon_ne_zero χ ψf μ v s
  -- the completed L-functions
  let Λ : ℂ → ℂ := fun s =>
    (∑ C, classFactor χ (classRepresentative C) s * (T C).M s) / (w * E s)
  let Λdual : ℂ → ℂ := fun s =>
    (∑ C, classFactor χ (classRepresentative C) (1 - s) * (T C).M (1 - s)) /
      (w * κc * E' s * ∏ v ∈ S, finiteEpsilon χ ψf μ v (1 - s))
  -- the thresholds
  set σI : ℝ := ∑ v, ‖(dR v).exponent‖ + ∑ v, ‖(dC v).exponent‖ with hσI_def
  refine ⟨max (max σA σf) (max σM σI), Λ, Λdual, S, ?_, ?_, ?_, ?_, ?_⟩
  · -- meromorphy of `Λ`
    intro z _
    have h1 : MeromorphicAt (fun s => ∑ C, classFactor χ (classRepresentative C) s * (T C).M s) z := by
      have := MeromorphicAt.sum (s := Finset.univ)
        (G := fun C s => classFactor χ (classRepresentative C) s * (T C).M s) (x := z)
        (fun C _ => ((differentiable_classFactor χ _).analyticAt z).meromorphicAt.mul
          ((T C).meromorphicOn_M z (Set.mem_univ z)))
      exact this.congr (Filter.Eventually.of_forall fun s => Finset.sum_apply _ _ _)
    exact h1.div ((analyticAt_const.mul (hEd.analyticAt z)).meromorphicAt)
  · -- meromorphy of `Λdual`
    intro z _
    have hsub : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
    have h1 : MeromorphicAt (fun s => ∑ C, classFactor χ (classRepresentative C) (1 - s) *
        (T C).M (1 - s)) z := by
      have := MeromorphicAt.sum (s := Finset.univ)
        (G := fun C s => classFactor χ (classRepresentative C) (1 - s) * (T C).M (1 - s)) (x := z)
        (fun C _ => (((differentiable_classFactor χ _).comp
          ((differentiable_const _).sub differentiable_id)).analyticAt z).meromorphicAt.mul
          (((T C).meromorphicOn_M (1 - z) (Set.mem_univ _)).comp_analyticAt hsub))
      exact this.congr (Filter.Eventually.of_forall fun s => Finset.sum_apply _ _ _)
    have hdiff : ∀ v, Differentiable ℂ (finiteEpsilon χ ψf μ v) :=
      finiteEpsilon_differentiable χ ψf μ
    have h2 : Differentiable ℂ (fun s => w * κc * E' s * ∏ v ∈ S, finiteEpsilon χ ψf μ v (1 - s)) := by
      fun_prop
    exact h1.div (h2.analyticAt z).meromorphicAt
  · -- the Euler products
    intro s hs
    obtain ⟨⟨hsA, hsf⟩, ⟨hsM, hsI⟩⟩ := (max_lt_iff.mp hs).imp max_lt_iff.mp max_lt_iff.mp
    obtain ⟨hsumN, -, hsumNF, hprod1, hprodinv, -, hfactor⟩ := hfin s hsf
    -- convergence of the archimedean integrals
    have hσR : ∀ v, ‖(dR v).exponent‖ ≤ σI := fun v => by
      have h1 := Finset.single_le_sum (f := fun v => ‖(dR v).exponent‖)
        (fun v _ => norm_nonneg _) (Finset.mem_univ v)
      have h2 := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC v).exponent)
      simp only [σI]
      linarith
    have hσC : ∀ v, ‖(dC v).exponent‖ ≤ σI := fun v => by
      have h1 := Finset.single_le_sum (f := fun v => ‖(dC v).exponent‖)
        (fun v _ => norm_nonneg _) (Finset.mem_univ v)
      have h2 := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR v).exponent)
      simp only [σI]
      linarith
    have hRint : ∀ v, 0 < (s + (dR v).exponent + (((dR v).parity : ℕ) : ℂ)).re := fun v => by
      have := Complex.abs_re_le_norm (dR v).exponent
      have := hσR v
      simp only [Complex.add_re, Complex.natCast_re]
      have := Nat.cast_nonneg (α := ℝ) ((dR v).parity : ℕ)
      linarith [abs_le.mp ‹|((dR v).exponent).re| ≤ _›]
    have hCint : ∀ v, 0 < (s + (dC v).exponent + (((dC v).weight.natAbs : ℂ)) / 2).re := fun v => by
      have := Complex.abs_re_le_norm (dC v).exponent
      have := hσC v
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      have := Nat.cast_nonneg (α := ℝ) ((dC v).weight.natAbs)
      linarith [abs_le.mp ‹|((dC v).exponent).re| ≤ _›]
    have hint := integrable_mixedGaussian_mul_mixedCharFun (fun v => (aR v : ℝ))
      (fun v => ((aC v : ℂˣ) : ℂ)) (fun v => (dR v).parity) (fun v => (dR v).exponent)
      (fun v => (dC v).weight) (fun v => (dC v).exponent) (fun v => (aR v).ne_zero)
      (fun v => (aC v).ne_zero) s hRint hCint
    have hprimal := sum_classFactor_mul_M aR aC dR dC χ hdR hdC T hTχ hTf s
      (fun C => by rw [hratio_eq]; exact (hσM s hsM).1) hsumN hint
    refine ⟨?_, ?_⟩
    · set Zs := ∫ y, gaussF aR aC dR dC y * mixedChar dR dC y *
        (mixedEmbedding.norm y : ℂ) ^ (s - 1) with hZs_def
      have hZs : Zs * infDen s = E s := hZ s hsA
      have hZne : Zs * infDen s ≠ 0 := hZs ▸ hE0 s
      have hval : Λ s * infDen s = finiteMellin χ s := by
        simp only [Λ]
        rw [hprimal, ← hZs]
        have h1 : Zs ≠ 0 := left_ne_zero_of_mul hZne
        have h2 : infDen s ≠ 0 := right_ne_zero_of_mul hZne
        field_simp
        rw [hw_def]
        ring
      rw [hval]
      exact hprod1
    · set ZG := ∫ y, gaussG aR aC dR dC y * mixedChar dR' dC' y *
        (mixedEmbedding.norm y : ℂ) ^ (s - 1) with hZG_def
      set Zh := ∫ x : mixedSpace K,
        Hecke.mixedGaussian (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
            (fun v => (dR v).parity) (-(fun v => (dC v).weight)) x *
          Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
            (fun v => (dC' v).weight) (fun v => (dC' v).exponent) x *
          ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1) with hZh_def
      have hZh : Zh * dualInfDen s = E' s := hZ' s hsA
      have hZhne : Zh * dualInfDen s ≠ 0 := hZh ▸ hE'0 s
      have hZG : ZG = κc * Zh := by
        rw [hZG_def, hZh_def, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [gaussG_eq, κc]
        ring
      have hRint' : ∀ v, 0 < (s + (-(fun v => (dR v).exponent)) v + (((dR v).parity : ℕ) : ℂ)).re :=
        fun v => by
          have := Complex.abs_re_le_norm (dR v).exponent
          have := hσR v
          simp only [Pi.neg_apply, Complex.add_re, Complex.neg_re, Complex.natCast_re]
          have := Nat.cast_nonneg (α := ℝ) ((dR v).parity : ℕ)
          linarith [abs_le.mp ‹|((dR v).exponent).re| ≤ _›]
      have hCint' : ∀ v, 0 < (s + (-(fun v => (dC v).exponent)) v +
          ((((-(fun v => (dC v).weight)) v).natAbs : ℂ)) / 2).re := fun v => by
        have := Complex.abs_re_le_norm (dC v).exponent
        have := hσC v
        simp only [Pi.neg_apply, Int.natAbs_neg, Complex.add_re, Complex.neg_re,
          Complex.div_ofNat_re, Complex.natCast_re]
        have := Nat.cast_nonneg (α := ℝ) ((dC v).weight.natAbs)
        linarith [abs_le.mp ‹|((dC v).exponent).re| ≤ _›]
      have hintG : Integrable fun y => gaussG aR aC dR dC y * mixedChar dR' dC' y *
          (mixedEmbedding.norm y : ℂ) ^ (s - 1) := by
        have h := (integrable_mixedGaussian_mul_mixedCharFun (fun v => (aR v : ℝ))
          (fun v => ((aC v : ℂˣ) : ℂ)) (fun v => (dR v).parity) (-(fun v => (dR v).exponent))
          (-(fun v => (dC v).weight)) (-(fun v => (dC v).exponent)) (fun v => (aR v).ne_zero)
          (fun v => (aC v).ne_zero) s hRint' hCint').const_mul κc
        refine h.congr (Filter.Eventually.of_forall fun y => ?_)
        simp only [mixedChar]
        rw [mixedCharFun_dual_eq_inv_apply χ dR dR' hdR hdR' dC dC' hdC hdC' y,
          Hecke.mixedCharFun_inv, gaussG_eq]
        simp only [κc]
        ring
      have hdual : ∀ C, classFactor χ (classRepresentative C) (1 - s) *
          ∫ x in fundamentalCone K, (Hecke.thetaSeries
            (fourierThetaCoeff χ ψf μ (classRepresentative C)) (gaussG aR aC dR dC) x⁻¹ -
              fourierThetaCoeff χ ψf μ (classRepresentative C) 0 * gaussG aR aC dR dC 0) *
                mixedChar dR dC x * (mixedEmbedding.norm x : ℂ) ^ (-s - 1) =
          (Units.torsionOrder K : ℂ) * ZG * ∑' p : principalDivisors K,
            DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
              (-(p : FinitePlaceDivisor K) - classRepresentative C) := by
        intro C
        obtain ⟨Sψ, hψ⟩ := exists_finset_additiveConductor_eq_zero ψ hdiag ψf hf aR hR aC hC
        obtain ⟨CG, cG, hcG, hGb⟩ := exists_gaussG_le aR aC dR dC
        exact classFactor_one_sub_mul_integral_fourierTheta χ ψf μ Sψ hψ dR dR' hdR hdR' dC dC'
          hdC hdC' (classRepresentative C) hcG hGb s S (fun v hv => hz v hv s) hsumNF hintG
      have hdualsum := sum_classFactor_one_sub_mul_M aR aC dR dC χ ψf μ T hTχ hTg s
        (fun C => by rw [hratio_eq]; exact (hσM s hsM).2) S hsumNF ZG hdual
      have hval : Λdual s * dualInfDen s = finiteMellin χ⁻¹ s := by
        simp only [Λdual]
        rw [hdualsum, hfactor, hZG, ← hZh]
        have h1 : Zh ≠ 0 := left_ne_zero_of_mul hZhne
        have h2 : dualInfDen s ≠ 0 := right_ne_zero_of_mul hZhne
        have h3 := hεne (1 - s)
        field_simp
        rw [hw_def]
        ring
      rw [hval]
      exact hprodinv
  · intro v hv s
    exact hε v hv s
  · -- the functional equation, for every `s`
    refine Filter.Eventually.of_forall fun s => ?_
    have hk := hEps s
    simp only [Λ, Λdual, sub_sub_cancel]
    have hden : w * κc * E' (1 - s) * ∏ v ∈ S, finiteEpsilon χ ψf μ v s =
        w * (infEps s * E s) * ∏ v ∈ S, finiteEpsilon χ ψf μ v s := by
      rw [← hk]
      ring
    change _ = (∏ v ∈ S, finiteEpsilon χ ψf μ v s) * infEps s * _
    rw [hden]
    have := hεne s
    have := hinfEps s
    have := hE0 s
    field_simp

end Langlands.Global
