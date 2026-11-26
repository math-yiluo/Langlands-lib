import Langlands.HarmonicAnalysis.Bicharacter.Fourier
import Langlands.HarmonicAnalysis.Distribution.Basic

/-! # Fourier restriction to a subgroup and its annihilator -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Function

universe u

variable {X : Type u} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [μ.IsAddHaarMeasure] {e : X → X → ℂ} (he : IsSelfDualBicharacter e)

/-- A test function supported in a subgroup has Fourier transform invariant under the
annihilator of the subgroup. -/
theorem bicharacterFourierSB_annihilatorInvariant (L : AddSubgroup X) (f : SchwartzBruhat X)
    (hf : support (f : X → ℂ) ⊆ L) (t : X) (ht : t ∈ he.annihilator (L : Set X)) (x : X) :
    bicharacterFourierSB μ he f (x + t) = bicharacterFourierSB μ he f x := by
  change (∫ y, e (x + t) y * f y ∂μ) = ∫ y, e x y * f y ∂μ
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : f y = 0
  · simp [hy]
  · have hty := (he.mem_annihilator.mp ht) y (hf hy)
    rw [he.map_add_left, he.symm t y, hty, mul_one]

variable [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X]

/-- If the Fourier transforms of two distributions agree on tests invariant under the
annihilator of a subgroup, the original distributions agree on tests supported in that
subgroup. The same Haar measure is used for both transforms. -/
def FourierRestrictionAgreementStatement (L : AddSubgroup X) (D D' : Distribution X) : Prop :=
  (∀ g : SchwartzBruhat X, (∀ t ∈ he.annihilator (L : Set X), ∀ x, g (x + t) = g x) →
    D (bicharacterFourierSB μ he g) = D' (bicharacterFourierSB μ he g)) →
  ∀ f : SchwartzBruhat X, support (f : X → ℂ) ⊆ L → D f = D' f

theorem Distribution.eq_of_fourierAgreement_on_annihilator (L : AddSubgroup X)
    (D D' : Distribution X) : FourierRestrictionAgreementStatement μ he L D D' := by
  intro h f hf
  let r := Hecke.TestFunction.pullback (Homeomorph.neg X) f
  have hr : support (r : X → ℂ) ⊆ L := by
    intro x hx
    have hneg : -x ∈ L := hf (show f (-x) ≠ 0 from hx)
    change x ∈ L
    simpa only [neg_neg] using L.neg_mem hneg
  let g := bicharacterFourierSB μ he r
  have hEq := h g (bicharacterFourierSB_annihilatorInvariant μ he L r hr)
  obtain ⟨c, hc, hInv⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ he
  have hFourier : bicharacterFourierSB μ he g = (c : ℂ) • f := by
    apply Subtype.ext
    funext x
    change bicharacterFourier μ e (bicharacterFourier μ e (r : X → ℂ)) x = (c : ℂ) * f x
    rw [hInv _ r.property x]
    change (c : ℂ) * f (- -x) = _
    rw [neg_neg]
  rw [hFourier, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hEq
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne') hEq

end Langlands.HarmonicAnalysis
