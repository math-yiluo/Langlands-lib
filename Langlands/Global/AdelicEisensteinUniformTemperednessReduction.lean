import Langlands.Global.AdelicEisensteinUniformTemperednessStatement
import Langlands.Global.AdelicUniformTemperednessCriterionStatement

/-! # Uniform temperedness of Eisenstein series from the criterion and the Eisenstein inputs

`EisensteinUniformTemperednessStatement` (Delorme 2023, Proposition 4.1) follows from the
uniform temperedness criterion `UniformTemperednessCriterionStatement`, the uniform moderate
growth `EisensteinUnitaryUniformGrowthStatement` and the subunitary exponents
`EisensteinUnitaryExponentStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic

/-- Delorme 2023, Proposition 4.1, from the uniform temperedness criterion applied to the
family `x ↦ E(i e(x))`, `x ∈ C`: the growth input supplies the family and its uniform moderate
growth, and the exponent input supplies the shift equations of its constant terms. -/
theorem eisensteinUniformTemperedness_of_criterion
    (hcrit : UniformTemperednessCriterionStatement)
    (hgrowth : EisensteinUnitaryUniformGrowthStatement)
    (hexp : EisensteinUnitaryExponentStatement) :
    EisensteinUniformTemperednessStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth
    hcalc φ hKmax hrho hφ E D hD hmer hreg n e C hC
  obtain ⟨L, R, f, hL, hfE, hfam⟩ :=
    hgrowth F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hD
      hmer hreg n e C hC
  obtain ⟨m, hm⟩ :=
    hexp F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hD
      hmer hreg n e C hC
  obtain ⟨k, hk⟩ := hcrit F G hG rho hsmooth hcalc hrho f C L R m hL hfam
    (fun 𝓕 J x hx => by rw [hfE x hx]; exact hm 𝓕 J x hx)
  refine ⟨k, fun T i ν T₀ j hsetup t Ω hΩ => ?_⟩
  obtain ⟨B, hB⟩ := hk T i ν T₀ j hsetup t Ω hΩ
  refine ⟨B, fun x hx z hz b hb ω hω => ?_⟩
  rw [← hfE x hx]
  exact hB x hx z hz b hb ω hω

end Langlands.Global
