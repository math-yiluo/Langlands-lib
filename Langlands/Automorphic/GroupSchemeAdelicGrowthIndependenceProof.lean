import Langlands.Automorphic.GroupSchemeAdelicGrowthIndependenceStatement
import Langlands.Global.AdelicRepresentationHeightDominationProof

/-! # Closed-embedding independence of full adelic growth conditions -/

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

private theorem transfer_height_bound {H K b C A : ℝ} {e k : ℕ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hdom : H ≤ A * K ^ e) (hb : b ≤ C * H ^ k) :
    b ≤ (C * A ^ k) * K ^ (e * k) := by
  calc
    b ≤ C * H ^ k := hb
    _ ≤ C * (A * K ^ e) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH hdom k) hC
    _ = (C * A ^ k) * K ^ (e * k) := by
      rw [mul_pow, ← pow_mul]
      ring

/-- Changing a positive-rank closed matrix embedding preserves ordinary and
uniform full adelic growth on the original function carriers. -/
theorem closedImmersionAdelicGrowthIndependence :
    ClosedImmersionAdelicGrowthIndependenceStatement.{u} := by
  have hdom := RepresentationGrowth.closedImmersionAdelicHeightDomination.{u}
  intro F _ _ G _ N M rho sigma hN hM hrho hsigma
  obtain ⟨A, hA, e, hboundSigma⟩ := hdom F G N M rho sigma hN hM hrho
  obtain ⟨B, hB, l, hboundRho⟩ := hdom F G M N sigma rho hM hN hsigma
  have hpoly (f : ContinuousRationalFunctions F G) :
      HasAdelicPolynomialGrowth F G rho f ↔ HasAdelicPolynomialGrowth F G sigma f := by
    constructor
    · rintro ⟨C, hC, k, hf⟩
      refine ⟨C * B ^ k, mul_nonneg hC (pow_nonneg (zero_le_one.trans hB) k),
        l * k, fun g => ?_⟩
      exact transfer_height_bound
        (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g))
        hC (hboundRho g) (hf g)
    · rintro ⟨C, hC, k, hf⟩
      refine ⟨C * A ^ k, mul_nonneg hC (pow_nonneg (zero_le_one.trans hA) k),
        e * k, fun g => ?_⟩
      exact transfer_height_bound
        (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G sigma hM g))
        hC (hboundSigma g) (hf g)
  constructor
  · intro f
    exact ⟨(hasAdelicModerateGrowth_iff F G rho hN f).trans
      ((hpoly f).trans (hasAdelicModerateGrowth_iff F G sigma hM f).symm), hpoly f⟩
  · intro d hsmooth hcalc f
    have huniform :
        HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f ↔
          HasAdelicUniformPolynomialGrowth F G sigma hsmooth hcalc f := by
      constructor
      · rintro ⟨k, hf⟩
        refine ⟨l * k, fun a => ?_⟩
        obtain ⟨C, hC, hf⟩ := hf a
        refine ⟨C * B ^ k, mul_nonneg hC (pow_nonneg (zero_le_one.trans hB) k),
          fun g => ?_⟩
        exact transfer_height_bound
          (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g))
          hC (hboundRho g) (hf g)
      · rintro ⟨k, hf⟩
        refine ⟨e * k, fun a => ?_⟩
        obtain ⟨C, hC, hf⟩ := hf a
        refine ⟨C * A ^ k, mul_nonneg hC (pow_nonneg (zero_le_one.trans hA) k),
          fun g => ?_⟩
        exact transfer_height_bound
          (zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G sigma hM g))
          hC (hboundSigma g) (hf g)
    exact ⟨(hasAdelicUniformModerateGrowth_iff F G rho hsmooth hcalc hN f).trans
      (huniform.trans
        (hasAdelicUniformModerateGrowth_iff F G sigma hsmooth hcalc hM f).symm), huniform⟩

end Langlands.Automorphic.GroupSchemeFunctions
