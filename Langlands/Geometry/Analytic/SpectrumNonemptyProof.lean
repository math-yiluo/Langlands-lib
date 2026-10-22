import Langlands.Geometry.Analytic.SpectrumNonemptyStatement
import Langlands.Geometry.Analytic.SpectralPowerBoundProof
import Mathlib.RingTheory.Ideal.Maximal

/-! # Constructing points of nonzero strict affinoid spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
private theorem one_le_scalar_norm_of_ne_zero
    (hK : ∀ c : K, ‖c‖ ≤ 1) {c : K} (hc : c ≠ 0) : 1 ≤ ‖c‖ := by
  calc
    1 = ‖c‖ * ‖c⁻¹‖ := by rw [← norm_mul, mul_inv_cancel₀ hc, norm_one]
    _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

private theorem tate_eq_zero_of_norm_lt_one
    (hK : ∀ c : K, ‖c‖ ≤ 1) {n : ℕ}
    (f : StrictTateAlgebra (Fin n) K) (hf : ‖f‖ < 1) : f = 0 := by
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  change MvPowerSeries.coeff d (StrictTateAlgebra.series (Fin n) K f) =
    MvPowerSeries.coeff d (0 : MvPowerSeries (Fin n) K)
  rw [map_zero]
  by_contra hc
  have h₁ := one_le_scalar_norm_of_ne_zero hK hc
  have h₂ := StrictTateAlgebra.norm_coeff_le (Fin n) K f d
  exact (not_lt_of_ge (h₁.trans h₂)) hf

/-- Over a trivially valued scalar field the actual quotient norm is at least
one on every nonzero element. This uses arbitrarily close representatives. -/
theorem one_le_norm_of_scalar_norm_le_one
    (P : PresentedStrictAffinoidAlgebra K) (hK : ∀ c : K, ‖c‖ ≤ 1)
    {a : P} (ha : a ≠ 0) : 1 ≤ ‖a‖ := by
  by_contra! h
  obtain ⟨f, hfa, hf⟩ :=
    exists_representative_norm_lt K P a (sub_pos.mpr h)
  have hf₁ : ‖f‖ < 1 := by linarith
  have hf₀ := tate_eq_zero_of_norm_lt_one hK f hf₁
  apply ha
  rw [← hfa, hf₀]
  exact map_zero (presentationMap K P).toAlgHom

/-- The trivial seminorm on an actual prime quotient, pulled back to the
original affinoid. No norm or closedness of that prime quotient is assumed. -/
def primePoint_of_scalar_norm_le_one
    (P : PresentedStrictAffinoidAlgebra K) (hK : ∀ c : K, ‖c‖ ≤ 1)
    (I : Ideal P) [I.IsPrime] : BanachSpectrum P := by
  classical
  let q := Ideal.Quotient.mk I
  let v : MulRingSeminorm (P ⧸ I) := 1
  exact
    { toFun := fun a => v (q a)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by simp
      add_le' := fun a b => by
        rw [map_add]
        exact map_add_le_add v _ _
      neg' := fun a => by simp
      le_norm := fun a => by
        change (1 : MulRingSeminorm (P ⧸ I)) (q a) ≤ ‖a‖
        rw [MulRingSeminorm.apply_one]
        split_ifs with h
        · exact norm_nonneg _
        · exact one_le_norm_of_scalar_norm_le_one P hK
            (fun ha => h (by rw [ha, map_zero])) }

/-- Trivially valued scalars yield a point by choosing an actual maximal ideal
and pulling back the trivial seminorm of its quotient domain. -/
theorem spectrum_nonempty_of_scalar_norm_le_one
    (P : PresentedStrictAffinoidAlgebra K) [Nontrivial P]
    (hK : ∀ c : K, ‖c‖ ≤ 1) : Nonempty (BanachSpectrum P) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (α := P)
  let : I.IsMaximal := hI
  exact ⟨primePoint_of_scalar_norm_le_one P hK I⟩

variable [CompleteSpace K]

/-- In the remaining case an empty spectrum would make the powers of a scalar
of norm greater than one bounded, contradicting geometric growth. -/
theorem spectrum_nonempty (P : PresentedStrictAffinoidAlgebra K)
    [Nontrivial P] : Nonempty (BanachSpectrum P) := by
  by_cases hK : ∀ c : K, ‖c‖ ≤ 1
  · exact spectrum_nonempty_of_scalar_norm_le_one P hK
  push Not at hK
  obtain ⟨c, hc⟩ := hK
  by_contra h
  obtain ⟨C, _hC, hbound⟩ := hasBoundedPowers_of_spectrum_le_one P
    (algebraMap K P c) (fun x => (h ⟨x⟩).elim)
  have h1 : 0 < ‖(1 : P)‖ := norm_pos_iff.mpr one_ne_zero
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖(1 : P)‖) hc
  have hgrowth : C < ‖c‖ ^ n * ‖(1 : P)‖ := (div_lt_iff₀ h1).mp hn
  have hb := hbound n
  rw [← map_pow, norm_algebraMap, norm_pow] at hb
  exact (not_lt_of_ge hb) hgrowth

/-- The closing theorem has the entire target proposition as its type. -/
theorem spectrumNonempty : SpectrumNonemptyStatement K := by
  intro P hP
  let := hP
  exact spectrum_nonempty P

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
