import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.OrdinaryLocalGrowthTransfer

/-! # Uniqueness of entire ordinary normalizations -/

noncomputable section

set_option autoImplicit false

open Filter Set Langlands.LocalFactor Langlands.LocalFactor.Archimedean

namespace Langlands.Global.RankinSelbergGlobal

/-- Entire normalized functions agreeing after multiplication by a common factor
on a right half-plane agree everywhere if that factor is eventually nonzero. -/
theorem OrdinaryIntegralNormalization.value_eq_of_factor_ne_zero {I L : ℂ → ℂ}
    (N N' : OrdinaryIntegralNormalization I L)
    (hL : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L s ≠ 0) : N.value = N'.value := by
  obtain ⟨b, hb⟩ := N.eq_on_right
  obtain ⟨b', hb'⟩ := N'.eq_on_right
  obtain ⟨c, hc⟩ := hL
  let a := max (max b b') c
  have ha : a < ((a + 1 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact lt_add_one _
  apply N.analytic.eq_of_eventuallyEq N'.analytic (z₀ := (a + 1 : ℝ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds ha] with s hs
  have hs' := (le_max_left (max b b') c).trans_lt hs
  exact mul_right_cancel₀ (hc s ((le_max_right _ _).trans_lt hs))
    ((hb s ((le_max_left _ _).trans_lt hs')).symm.trans (hb' s ((le_max_right _ _).trans_lt hs')))

/-- One entire normalization with a strip growth bound for each test supplies
ordinary continuation and the estimate for every entire normalization. -/
def OrdinaryNormalizationGrowthFromExistenceStatement : Prop :=
  ∀ {Test : Type*} (I : Test → ℂ → ℂ) (L : ReciprocalEntire),
    (∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0) →
    (∀ i, ∃ N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹),
      HasStripExponentialGrowth N.value) →
      HasEntireOrdinaryNormalizations I L ∧ HasOrdinaryNormalizationStripGrowth I L

theorem ordinaryNormalizationGrowthFromExistence : OrdinaryNormalizationGrowthFromExistenceStatement := by
  intro Test I L hL hN
  refine ⟨fun i => ⟨(hN i).choose⟩, fun i N => ?_⟩
  obtain ⟨b, hb⟩ := hL
  obtain ⟨N', hN'⟩ := hN i
  rw [N.value_eq_of_factor_ne_zero N' ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩]
  exact hN'

end Langlands.Global.RankinSelbergGlobal
