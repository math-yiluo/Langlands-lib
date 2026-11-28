import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Integration and pairing of square-integrable fibres -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory

namespace Langlands.Analysis

variable {U V Q : Type*} [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace Q]
  {α : Measure U} {β : Measure V} {μ : Measure Q}
  [IsFiniteMeasure α] [IsFiniteMeasure β] [SFinite μ]

private theorem sq_norm_integral_le {f : U → ℂ} (hf : MemLp f 2 α) :
    ‖∫ u, f u ∂α‖ ^ 2 ≤ α.real Set.univ * ∫ u, ‖f u‖ ^ 2 ∂α := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := α) Real.HolderConjugate.two_two
    (f := f) (g := fun _ => (1 : ℝ)) (by simpa using hf) (by simp [memLp_const])
  have hnorm : ‖∫ u, f u ∂α‖ ≤
      Real.sqrt (∫ u, ‖f u‖ ^ 2 ∂α) * Real.sqrt (α.real Set.univ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa [Real.rpow_two, Real.sqrt_eq_rpow, smul_eq_mul] using h
  calc
    _ ≤ (Real.sqrt (∫ u, ‖f u‖ ^ 2 ∂α) * Real.sqrt (α.real Set.univ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
        Real.sq_sqrt (by positivity), mul_comm]

/-- Integrating out a finite measure factor preserves square integrability in the other factor. -/
theorem memLp_two_integral_fst {f : U × Q → ℂ} (hf : MemLp f 2 (α.prod μ)) :
    MemLp (fun q => ∫ u, f (u, q) ∂α) 2 μ := by
  have hm := hf.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hs := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  refine (memLp_two_iff_integrable_sq_norm hm).mpr
    ((hs.integral_prod_right.const_mul (α.real Set.univ)).mono' (hm.norm.pow 2) ?_)
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hs.prod_left_ae] with q hqm hqi
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_norm_integral_le ((memLp_two_iff_integrable_sq_norm hqm).mpr hqi)

/-- The integral of the pairings of two square-integrable families on finite measure spaces
is the pairing of their fibre integrals. -/
def SquareIntegrableFibrePairingStatement : Prop :=
  ∀ {U V Q : Type*} [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace Q]
    (α : Measure U) (β : Measure V) (μ : Measure Q)
    [IsFiniteMeasure α] [IsFiniteMeasure β] [SFinite μ]
    (f : U × Q → ℂ) (g : V × Q → ℂ),
    MemLp f 2 (α.prod μ) → MemLp g 2 (β.prod μ) →
    Integrable (fun p : U × V => ∫ q, f (p.1, q) * (starRingEnd ℂ) (g (p.2, q)) ∂μ)
      (α.prod β) ∧
    (∫ q, (∫ u, f (u, q) ∂α) * (starRingEnd ℂ) (∫ v, g (v, q) ∂β) ∂μ) =
      ∫ u, ∫ v, ∫ q, f (u, q) * (starRingEnd ℂ) (g (v, q)) ∂μ ∂β ∂α

/-- Pull both families to the three-factor measure, use Hölder and integrate in both orders. -/
theorem squareIntegrableFibrePairing : SquareIntegrableFibrePairingStatement := by
  intro U V Q _ _ _ α β μ _ _ _ f g hf hg
  let swap : (U × V) × Q ≃ᵐ (V × U) × Q :=
    MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl Q)
  have hswap : MeasurePreserving swap ((α.prod β).prod μ) ((β.prod α).prod μ) :=
    (Measure.measurePreserving_swap (μ := α) (ν := β)).prod (MeasurePreserving.id μ)
  have hF : MemLp (fun p : (U × V) × Q => f (p.1.1, p.2)) 2 ((α.prod β).prod μ) :=
    (hf.comp_snd β).comp_measurePreserving ((measurePreserving_prodAssoc β α μ).comp hswap)
  have hG : MemLp (fun p : (U × V) × Q => g (p.1.2, p.2)) 2 ((α.prod β).prod μ) :=
    (hg.comp_snd α).comp_measurePreserving (measurePreserving_prodAssoc α β μ)
  let H (p : (U × V) × Q) : ℂ := f (p.1.1, p.2) * (starRingEnd ℂ) (g (p.1.2, p.2))
  have hH : Integrable H ((α.prod β).prod μ) := hF.integrable_mul hG.star
  refine ⟨hH.integral_prod_left, ?_⟩
  calc
    _ = ∫ p, H p ∂(α.prod β).prod μ := by
      rw [integral_prod_symm H hH]
      apply integral_congr_ae (Eventually.of_forall fun q => ?_)
      rw [← integral_conj]
      exact (integral_prod_mul (μ := α) (ν := β) (fun u => f (u, q))
        (fun v => (starRingEnd ℂ) (g (v, q)))).symm
    _ = _ := by
      rw [integral_prod H hH, integral_prod _ hH.integral_prod_left]

end Langlands.Analysis
