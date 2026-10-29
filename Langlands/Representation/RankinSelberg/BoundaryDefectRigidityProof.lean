import Langlands.Representation.RankinSelberg.BoundaryDefectRigidityStatement
import Langlands.Representation.RankinSelberg.ReflectionRigidityProof

namespace Langlands.RankinSelberg

open Polynomial

theorem boundaryDefectRigidity : BoundaryDefectRigidityStatement := by
  intro a b δ c m A C P D Adual Cdual Pdual E ha hb hgap hA0 hC0 hP0 hAd0 hCd0 hPd0
    hprod hprodd hAP hAPd hC hCd hid
  obtain ⟨S, rfl⟩ := hAP
  obtain ⟨Sd, rfl⟩ := hAPd
  have hA : A ≠ 0 := fun h => by simp [h] at hA0
  have hAd : Adual ≠ 0 := fun h => by simp [h] at hAd0
  have hCDS : C = D * S := mul_left_cancel₀ hA (by rw [hprod]; ring)
  have hCdES : Cdual = E * Sd := mul_left_cancel₀ hAd (by rw [hprodd]; ring)
  have hD0 : D.coeff 0 = 1 := by
    have hS0 : S.coeff 0 = 1 := by simpa [mul_coeff_zero, hA0] using hP0
    have h := congrArg (fun p : ℂ[X] => p.coeff 0) hprod
    simpa [mul_coeff_zero, hA0, hC0, hS0] using h.symm
  have hE0 : E.coeff 0 = 1 := by
    have hSd0 : Sd.coeff 0 = 1 := by simpa [mul_coeff_zero, hAd0] using hPd0
    have h := congrArg (fun p : ℂ[X] => p.coeff 0) hprodd
    simpa [mul_coeff_zero, hAd0, hCd0, hSd0] using h.symm
  have hDroots : ∀ z : ℂ, ‖z‖ < a → D.eval z ≠ 0 := fun z hz hDz =>
    hC z hz (by rw [hCDS, eval_mul, hDz, zero_mul])
  have hEroots : ∀ z : ℂ, ‖z‖ < b → E.eval z ≠ 0 := fun z hz hEz =>
    hCd z hz (by rw [hCdES, eval_mul, hEz, zero_mul])
  obtain ⟨hD1, hE1⟩ :=
    reflectionRigidity a b δ c m D E ha hb hgap hD0 hE0 hDroots hEroots hid
  refine ⟨hD1, hE1, ?_, ?_⟩
  · rw [hprod, hD1, one_mul]
  · rw [hprodd, hE1, one_mul]

end Langlands.RankinSelberg
