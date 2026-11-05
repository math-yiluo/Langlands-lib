import Langlands.LinearAlgebra.ValuativeSpectralIntegralityStatement
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Valuative coefficient and root integrality -/

noncomputable section

universe u v

open Polynomial

namespace Langlands

private theorem isIntegral_valuationInteger_iff
    {K : Type*} [Field K] [ValuativeRel K] (x : K) :
    IsIntegral (ValuativeRel.valuation K).integer x ↔ x ≤ᵥ (1 : K) := by
  rw [(Valuation.integer.integers (ValuativeRel.valuation K)).isIntegral_iff_v_le_one]
  simpa only [map_one] using
    ((ValuativeRel.valuation K).vle_iff_le (x := x) (y := 1)).symm

/-- Over a valuative field, monic split polynomials have integral coefficients
exactly when all their roots are integral. -/
theorem coeff_vle_one_iff_roots_vle_one
    {K : Type*} [Field K] [ValuativeRel K] (p : Polynomial K)
    (hp : p.Monic) (hs : p.Splits) :
    (∀ i : ℕ, p.coeff i ≤ᵥ (1 : K)) ↔
      ∀ x : K, p.IsRoot x → x ≤ᵥ (1 : K) := by
  let O := (ValuativeRel.valuation K).integer
  constructor
  · intro hc x hx
    have hl : p ∈ Polynomial.lifts (algebraMap O K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      exact ⟨⟨p.coeff i, by
        exact (ValuativeRel.valuation K).vle_iff_le.mp (hc i)⟩, rfl⟩
    obtain ⟨q, hq, _, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
    apply (isIntegral_valuationInteger_iff x).mp
    refine ⟨q, hqm, ?_⟩
    have hroot : p.eval x = 0 := hx
    rw [← hq, Polynomial.eval_map_algebraMap] at hroot
    exact hroot
  · intro hr i
    apply (isIntegral_valuationInteger_iff (p.coeff i)).mp
    exact Polynomial.isIntegral_coeff_of_factors p
      (by simpa only [hp.leadingCoeff] using (isIntegral_one : IsIntegral O (1 : K)))
      hs (fun x hx => (isIntegral_valuationInteger_iff x).mpr (hr x hx)) i

/-- The scalar comparison in an arbitrary compatible valued splitting extension. -/
theorem valuativePolynomialRoots_proof : ValuativePolynomialRootsStatement.{u, v} := by
  intro F E _ _ _ _ _ _ p hp hs
  have hc : (∀ i : ℕ, p.coeff i ≤ᵥ (1 : F)) ↔
      ∀ i : ℕ, (p.map (algebraMap F E)).coeff i ≤ᵥ (1 : E) := by
    simp only [Polynomial.coeff_map, ← map_one (algebraMap F E),
      ValuativeExtension.vle_iff_vle]
  exact hc.trans (coeff_vle_one_iff_roots_vle_one _ (hp.map _) hs)

/-- The matrix comparison follows from the scalar comparison and characteristic
polynomial compatibility with scalar extension. -/
theorem valuativeMatrixRoots_proof : ValuativeMatrixRootsStatement.{u, v} := by
  intro F E _ _ _ _ _ _ N A hs
  have hmap := Matrix.charpoly_map A (algebraMap F E)
  rw [hmap] at hs ⊢
  exact valuativePolynomialRoots_proof F E A.charpoly A.charpoly_monic hs

/-- Exact proof of both published-valuative spectral bridge targets. -/
theorem valuativeSpectralIntegrality_proof :
    ValuativeSpectralIntegralityStatement.{u, v} :=
  ⟨valuativePolynomialRoots_proof, valuativeMatrixRoots_proof⟩

end Langlands
