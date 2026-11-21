import Langlands.Global.RankinSelberg.OrdinaryNormalizationStripGrowth

/-! # Local ordinary normalization and growth of its products -/

noncomputable section

set_option autoImplicit false

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean Set

namespace Langlands.Global.RankinSelbergGlobal

/-- Every entire ordinary normalization for the given integral family has exponential strip growth. -/
def HasOrdinaryNormalizationStripGrowth {Test : Type*} (I : Test → ℂ → ℂ) (L : ReciprocalEntire) : Prop :=
  ∀ (i : Test) (N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹)),
    HasStripExponentialGrowth N.value

theorem hasOrdinaryNormalizationStripGrowth_real_of_raw {Test : Type*} (I : Test → ℂ → ℂ)
    (d e : List RealBlock)
    (h : ∀ i, ∃ M : ℂ → ℂ, MeromorphicOn M univ ∧ HasStripExponentialGrowth M ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → I i s = M s) :
    HasOrdinaryNormalizationStripGrowth I (realPairLFactor d e) := by
  intro i N
  obtain ⟨M, hM, hMG, hI⟩ := h i
  exact N.stripGrowth_realPair hM hMG hI

theorem hasOrdinaryNormalizationStripGrowth_complex_of_raw {Test : Type*} (I : Test → ℂ → ℂ)
    (d e : List ComplexCharacterData)
    (h : ∀ i, ∃ M : ℂ → ℂ, MeromorphicOn M univ ∧ HasStripExponentialGrowth M ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → I i s = M s) :
    HasOrdinaryNormalizationStripGrowth I (complexPairLFactor d e) := by
  intro i N
  obtain ⟨M, hM, hMG, hI⟩ := h i
  exact N.stripGrowth_complexPair hM hMG hI

/-- An ordinary normalization bounded on every closed vertical strip has exponent zero. -/
theorem stripGrowth_of_norm_bounded_on_strips {f : ℂ → ℂ}
    (h : ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C) :
    HasStripExponentialGrowth f := by
  intro a b
  obtain ⟨C, hC⟩ := h a b
  refine ⟨max C 0, 0, 0, le_max_right _ _, le_rfl, fun s ha hb _ => ?_⟩
  simpa only [zero_mul, Real.exp_zero, mul_one] using (hC s ha hb).trans (le_max_left _ _)

/-- The real, complex and retained finite products of normalized values retain the
exponential strip bound after multiplication by a fixed scalar. -/
theorem stripGrowth_of_local_normalized_products {R C V : Type*} [Fintype R] [Fintype C] [Fintype V]
    (f : R → ℂ → ℂ) (g : C → ℂ → ℂ) (h : V → ℂ → ℂ) (k : ℂ)
    (hf : ∀ v, HasStripExponentialGrowth (f v)) (hg : ∀ w, HasStripExponentialGrowth (g w))
    (hh : ∀ v, HasStripExponentialGrowth (h v)) :
    HasStripExponentialGrowth (fun s => k * (((∏ v, f v s) * ∏ w, g w s) * ∏ v, h v s)) := by
  have hf' := normalizedProductStripGrowth R Finset.univ f k (fun v _ => hf v)
  have hg' := normalizedProductStripGrowth C Finset.univ g 1 (fun w _ => hg w)
  have hh' := normalizedProductStripGrowth V Finset.univ h 1 (fun v _ => hh v)
  simpa only [Pi.mul_def, one_mul, mul_assoc] using (hf'.mul hg').mul hh'

end Langlands.Global.RankinSelbergGlobal
