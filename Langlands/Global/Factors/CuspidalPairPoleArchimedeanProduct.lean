import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Global.Factors.CuspidalPairPoleStatement

/-! # The initial archimedean product for cuspidal pairs -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairPoles

open NumberField LocalFactor LocalFactor.Archimedean
open FunctionalEquationComparison.CompletedEquationAdapter

variable {F : Type u} [Field F] [NumberField F]

/-- The archimedean factor function in the pole statement. -/
def archimedeanPairProduct
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData) (s : ℂ) : ℂ := by
  classical
  exact (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
    ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹

private theorem analyticOnNhd_prod_inv_denominator {ι : Type*} [Fintype ι]
    (G : ι → ReciprocalEntire)
    (h : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (G i).denominator s ≠ 0) :
    ∃ σ : ℝ, AnalyticOnNhd ℂ (fun s => ∏ i, ((G i).denominator s)⁻¹) {s | σ < s.re} := by
  classical
  choose σ hσ using h
  refine ⟨∑ i, |σ i|, fun s hs => Finset.analyticAt_fun_prod Finset.univ fun i hi => ?_⟩
  have hiσ : σ i ≤ ∑ j, |σ j| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |σ j|) (fun j _ => abs_nonneg _) hi)
  exact ((G i).entire.analyticAt s).inv (hσ i s (hiσ.trans_lt hs))

/-- The specified product of archimedean L-factors is analytic on a common right half-plane. -/
theorem archimedeanPairProduct_analyticOnNhd_right
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData) :
    ∃ σ : ℝ, AnalyticOnNhd ℂ (archimedeanPairProduct dR dR' dC dC') {s | σ < s.re} := by
  classical
  obtain ⟨a, ha⟩ := analyticOnNhd_prod_inv_denominator (fun v => realPairLFactor (dR v) (dR' v))
    (fun v => realPairLFactor_denominator_ne_zero (dR v) (dR' v))
  obtain ⟨b, hb⟩ := analyticOnNhd_prod_inv_denominator (fun v => complexPairLFactor (dC v) (dC' v))
    (fun v => complexPairLFactor_denominator_ne_zero (dC v) (dC' v))
  refine ⟨max a b, fun s hs => ?_⟩
  exact (ha s (lt_of_le_of_lt (le_max_left a b) hs)).fun_mul
    (hb s (lt_of_le_of_lt (le_max_right a b) hs))

/-- Multiplying the archimedean product by a finite Euler product continuous on a
right half-plane gives a continuous initial completed product on a right half-plane. -/
theorem exists_continuousOn_archimedeanPairProduct_mul
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    {Lfin : ℂ → ℂ} (hLfin : ∃ σ : ℝ, ContinuousOn Lfin {s | σ < s.re}) :
    ∃ σ : ℝ, ContinuousOn (fun s => archimedeanPairProduct dR dR' dC dC' s * Lfin s)
      {s | σ < s.re} := by
  obtain ⟨a, ha⟩ := archimedeanPairProduct_analyticOnNhd_right dR dR' dC dC'
  obtain ⟨b, hb⟩ := hLfin
  exact ⟨max a b, (ha.continuousOn.mono fun _ hs => (le_max_left a b).trans_lt hs).mul
    (hb.mono fun _ hs => (le_max_right a b).trans_lt hs)⟩

end Langlands.Global.CuspidalPairPoles
