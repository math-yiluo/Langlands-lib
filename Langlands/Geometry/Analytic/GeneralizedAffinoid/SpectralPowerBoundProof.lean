import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectralPowerBoundStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RadiusRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChange
import Langlands.Geometry.Analytic.SpectralPowerBoundProof
import Langlands.Geometry.Analytic.AffinoidUnitNorm

/-! # Spectral bounds give radius-weighted power bounds in affinoid quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Reduction to the radius-one strict theorem: a ring map into a strict
presentation over a larger field, which is contractive and bounded below, together
with a field element of norm `r`, transports the spectral hypothesis. -/
theorem hasRadiusBoundedPowers_of_strict_comparison
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (P : PresentedAffinoidAlgebra K) (a : P) {r : ℝ} (hr : 0 < r)
    (ha : ∀ x : BanachSpectrum P, x a ≤ r) (c : L) (hc : ‖c‖ = r)
    (Q : PresentedStrictAffinoidAlgebra L) (ψ : P →+* Q) {C : ℝ} (hC : 0 < C)
    (hψ : ∀ x, ‖ψ x‖ ≤ ‖x‖) (hψ' : ∀ x, ‖x‖ ≤ C * ‖ψ x‖) :
    HasRadiusBoundedPowers r a := by
  let ψb : BoundedRingHom P Q := ⟨ψ, ⟨1, zero_lt_one, fun x => by rw [one_mul]; exact hψ x⟩⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hc
    exact hr.ne hc
  have halg : ∀ z : L, ‖algebraMap L Q z‖ ≤ ‖z‖ := fun z => by
    rw [_root_.norm_algebraMap]
    exact mul_le_of_le_one_right (norm_nonneg z) Q.quotient_norm_one_le
  let b : Q := algebraMap L Q c⁻¹ * ψ a
  have hb : ∀ y : BanachSpectrum Q, y b ≤ 1 := by
    intro y
    have h1 : y (algebraMap L Q c⁻¹) ≤ r⁻¹ :=
      (y.le_norm _).trans ((halg _).trans_eq (by rw [norm_inv, hc]))
    have h2 : y (ψ a) ≤ r := ha (BanachSpectrum.comap ψb y)
    calc
      y b = y (algebraMap L Q c⁻¹) * y (ψ a) := map_mul y.toMulRingSeminorm _ _
      _ ≤ r⁻¹ * r := mul_le_mul h1 h2 (apply_nonneg y.toMulRingSeminorm _)
          (inv_pos.mpr hr).le
      _ = 1 := inv_mul_cancel₀ hr.ne'
  obtain ⟨D, hD, hDb⟩ := PresentedStrictAffinoidAlgebra.hasBoundedPowers_of_spectrum_le_one Q b hb
  refine ⟨C * D, mul_pos hC hD, fun n => ?_⟩
  have hψn : ψ (a ^ n) = algebraMap L Q (c ^ n) * b ^ n := by
    have hcc : algebraMap L Q (c ^ n) * algebraMap L Q c⁻¹ ^ n = 1 := by
      rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc0, one_pow, map_one]
    show ψ (a ^ n) = algebraMap L Q (c ^ n) * (algebraMap L Q c⁻¹ * ψ a) ^ n
    rw [map_pow, mul_pow, ← mul_assoc, hcc, one_mul]
  calc
    ‖a ^ n‖ ≤ C * ‖ψ (a ^ n)‖ := hψ' _
    _ ≤ C * (r ^ n * D) := by
      rw [hψn]
      apply mul_le_mul_of_nonneg_left _ hC.le
      calc
        ‖algebraMap L Q (c ^ n) * b ^ n‖ ≤ ‖algebraMap L Q (c ^ n)‖ * ‖b ^ n‖ := norm_mul_le _ _
        _ ≤ r ^ n * D := by
          apply mul_le_mul _ (hDb n) (norm_nonneg _) (pow_pos hr n).le
          exact (halg _).trans_eq (by rw [norm_pow, hc])
    _ = C * D * r ^ n := by ring

/-- Pointwise spectral bounds at a positive radius give radius-weighted bounded powers
in every finite positive-polyradius quotient presentation over a complete ultrametric
field. -/
theorem spectralPowerBound [CompleteSpace K] : SpectralPowerBoundStatement K := by
  intro P a r hr ha
  obtain ⟨R⟩ := RadiusRealization.nonempty (K := K) (P.arity + 1)
    (Fin.cons r P.polyradius) (Fin.cases hr P.polyradius.positive)
  obtain ⟨Q, ψ, C, hC, hψ, hψ'⟩ := exists_strictBaseChange R.ι R.norm_ι R.π R.π_ι_mul R.π_one
    R.bound_pos R.norm_π_le P (fun i => R.c i.succ) (fun i => R.norm_c i.succ)
  exact hasRadiusBoundedPowers_of_strict_comparison P a hr ha (R.c 0) (R.norm_c 0) Q ψ hC hψ hψ'

end Langlands.Analytic.PresentedAffinoidAlgebra
