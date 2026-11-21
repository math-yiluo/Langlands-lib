import Langlands.Global.Factors.CuspidalIsobaricPoleOrderReduction
import Langlands.Global.Factors.CuspidalPairLandauOrders
import Langlands.Global.Factors.CuspidalPairAbsoluteConvergence

/-! # The cuspidal-isobaric pole order from completed pair poles -/

noncomputable section

set_option autoImplicit false

universe u uQ

open Filter Topology

namespace Langlands.Global

open NumberField
open Automorphic (OperatorRealization)
open CuspidalIsobaricPoles (PartialPairNonvanishingAtOne)
open CuspidalPairAbsoluteConvergence (logEulerTerm)
open CuspidalPairLandauOrders (landauAsymptoticsReduction)
open CuspidalPairPartialContinuation

private theorem order_eq_of_normalizedLog {L : ℂ → ℂ} {l : ℝ → ℂ} {n : ℤ}
    (hL : MeromorphicAt L 1) (hl : ContinuousOn l (Set.Ioo 1 2))
    (hexp : ∀ σ ∈ Set.Ioo (1 : ℝ) 2, Complex.exp (l σ) = L (σ : ℂ))
    (hlimit : Tendsto (fun σ : ℝ => l σ / (Real.log (1 / (σ - 1)) : ℂ))
      (𝓝[>] 1) (𝓝 (-(n : ℂ)))) : meromorphicOrderAt L 1 = n := by
  have hRay : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Set.Ioi 1)] with σ hσ
      exact Set.mem_compl_singleton_iff.mpr (by exact_mod_cast (Set.mem_Ioi.mp hσ).ne')
  have hfinite : meromorphicOrderAt L 1 ≠ ⊤ := by
    intro htop
    obtain ⟨σ, hz, hσ⟩ := ((hRay.eventually (meromorphicOrderAt_eq_top_iff.mp htop)).and
      (Ioo_mem_nhdsGT (show (1 : ℝ) < 2 from one_lt_two))).exists
    exact Complex.exp_ne_zero (l σ) ((hexp σ hσ).trans hz)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hmlimit := LogarithmicAsymptotics.tendsto_div_log_of_meromorphicOrderAt
    (f := L) (θ := 0) (n := m) (by simpa using hL) (by simpa using hm.symm)
    (a := 2) one_lt_two hl (by simpa using hexp)
  have hmn : m = n := by
    exact_mod_cast (neg_inj.mp (tendsto_nhds_unique hmlimit hlimit))
  rw [← hm, hmn]

private theorem partialPairNonvanishingAtOne_of_logAsymptotics
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hconv : CuspidalPairAbsoluteConvergenceStatement.{u, uQ})
    (hpartial : PartialPairContinuationAt.{u, uQ} F)
    (hasymptotics : CuspidalPairLogAsymptoticsAt.{u, uQ} F) :
    PartialPairNonvanishingAtOne.{u, uQ} F := by
  intro r t T T' hTs hTs' P P' h h' S hP hP'
  have hT := cuspidalSplitCentreUnitaryCentralCharacter F r T hTs
  have hT' := cuspidalSplitCentreUnitaryCentralCharacter F t T' hTs'
  obtain ⟨L, hexp, hL, -⟩ := hpartial r t T T' hT hT' hTs hTs' P P' h h' S hP hP'
  refine ⟨L, hL, ?_⟩
  let l (σ : ℝ) := ∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
    logEulerTerm P P' hP hP' x.1 x.2 (σ : ℂ)
  have hl : ContinuousOn l (Set.Ioo 1 2) :=
    (differentiableOn_logSeries P P' hP hP' (fun σ hσ =>
      (hconv F r t T T' hT hT' P P' S hP hP' (σ : ℂ) (by simpa using hσ)).1)).continuousOn.comp
        Complex.continuous_ofReal.continuousOn (fun σ hσ => by
          change 1 < (σ : ℂ).re
          simpa only [Complex.ofReal_re] using hσ.1)
  have hExp (σ : ℝ) (hσ : σ ∈ Set.Ioo (1 : ℝ) 2) : Complex.exp (l σ) = L (σ : ℂ) :=
    (hexp _ (by simpa using hσ.1)).symm
  have hmer := hL.1 1 (Set.mem_univ 1)
  have hlimits := hasymptotics r t T T' hT hT' hTs hTs' P P' h h' S hP hP' (0 : ℝ)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, true_and] at hlimits
  by_cases hd : ∃ hrt : r = t,
    OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) T'.realization
  · have horder := order_eq_of_normalizedLog (n := -1) hmer hl hExp (by simpa using hlimits.1 hd)
    rw [horder]
    decide
  · have horder := order_eq_of_normalizedLog (n := 0) hmer hl hExp (by simpa using hlimits.2 hd)
    rw [horder]
    decide

/-- The completed cuspidal pair pole statement implies the isobaric pole order. -/
def CuspidalIsobaricPoleOrderLandauReductionStatement : Prop :=
  CuspidalPairPoleStatement.{u, uQ} → CuspidalIsobaricPoleOrderStatement.{u, uQ}

theorem cuspidalIsobaricPoleOrderLandauReduction :
    CuspidalIsobaricPoleOrderLandauReductionStatement.{u, uQ} := by
  intro hPair
  apply cuspidalIsobaricPoleOrder_of_partialPairNonvanishingAtOne hPair
  intro F _ _ _
  have hconv := cuspidalPairAbsoluteConvergence.{u, uQ}
  have hpartial := (partialPairContinuationReduction hconv).1 hPair F
  exact partialPairNonvanishingAtOne_of_logAsymptotics hconv hpartial
    (landauAsymptoticsReduction hconv F hpartial)

end Langlands.Global
