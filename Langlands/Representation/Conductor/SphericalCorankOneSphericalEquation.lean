import Langlands.Representation.Conductor.SphericalCorankOneIntegrals
import Langlands.Representation.Conductor.SphericalCorankOneGammaAlgebra
import Langlands.Representation.Conductor.SphericalDualParameters

/-!
# The spherical corank-one functional equation from a pair gamma factor

Over an arbitrary nonarchimedean local field, let `π` be a representation of
`GL_(n+2)(F)` and `σ` a representation of `GL_(n+1)(F)` whose model for an inverse
Whittaker functional `λ` contains Jacquet's spherical function `W(·; x; ψ̄)` and on which
`-1` acts by the scalar `1`. If `rationalGammaExpression δ C M Q Q̃` is the gamma factor of
`π × σ`, then the corank-one integrals of the coefficient of `v` against `W(·; x; ψ̄)`, and
of the coefficient of `v` for the dual functional against `W(·; x⁻¹; ψ)`, have rational
continuations satisfying the normalized functional equation with polynomials `Q`, `Q̃`,
epsilon monomial `C X^M` and no extra exponent. This is the step of
Jacquet, Piatetski-Shapiro and Shalika 1981, Section (4.2), printed pages 208-209, which
specializes the functional equation (1) to the spherical functions of display (3).
-/

noncomputable section

namespace Langlands.Conductor.SphericalCorankOne

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial
open Langlands.RankinSelberg Langlands.GeneralLinear.Iwasawa

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- JPSS 1981, Section (4.2), printed pages 208-209: a gamma factor
`rationalGammaExpression δ C M Q Q̃` of `π × σ`, where the model of `σ` for a nonzero
inverse Whittaker functional `λ` contains `W(·; x; ψ̄)` and `-1` acts on it by `1`, gives
rational continuations `R`, `R̃` of the corank-one integral of the coefficient of `v` for
`ℓ` against `W(·; x; ψ̄)` and of the coefficient of `v` for the dual functional `ℓ'`
against `W(·; x⁻¹; ψ)`, satisfying the normalized functional equation with `Q`, `Q̃`,
`C X^M`, scalar `1` and exponent `0`. -/
theorem normalizedFunctionalEquation_of_sphericalGammaFactor
    {q : ℕ} (hq : 1 < q) {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
    {ν : AdditiveHaarMeasure F} {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    {C : ℂˣ} {M : ℤ} {Q Qdual : ℂ[X]} (hQd : Qdual ≠ 0)
    (hG : IsPairGammaFactor q ψ abv ν π σ (rationalGammaExpression δ C M Q Qdual))
    [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π))
    (hℓ' : ℓ'.val = (dualFunctional ψ π ℓ).val)
    (lam : glInverseFunctionals ψ n σ) (hlam : lam.val ≠ 0)
    (hσ1 : HasModelMinusOneScalar σ lam 1)
    (hψ : ∀ y ∈ (ValuativeRel.valuation F).integer, ψ y = 1)
    (hψ' : ∀ y ∈ (ValuativeRel.valuation F).integer, ψ.scale (-1) y = 1)
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (x : Fin (n + 1) → ℂˣ)
    (hx : inverseSphericalWhittaker hψ hϖ q x ∈ (coefficientModel σ lam).toSubmodule)
    (v : V) :
    ∃ R Rdual : RationalFunctions,
      HasRationalContinuation q
        (corankOneIntegral ψ abv μ (coefficientMap π ℓ v)
          (inverseSphericalWhittaker hψ hϖ q x)) R ∧
      HasRationalContinuation q
        (corankOneIntegral (ψ.scale (-1)) abv μ
          (coefficientMap (inverseTransposePullback π) ℓ' v)
          (inverseSphericalWhittaker hψ' hϖ q x⁻¹)) Rdual ∧
      NormalizedFunctionalEquation q Q Qdual 1 C 0 M R Rdual := by
  have hℓ'eq : ℓ' = firstDualFunctional ψ π ℓ := Subtype.ext hℓ'
  subst hℓ'eq
  obtain ⟨ζ, hζ, R, Rd, hR, hRd, hN⟩ :=
    corankOne_gammaFunctionalEquation hG μ hμ ℓ hℓ lam hlam
      ⟨coefficientMap π ℓ v, ⟨v, rfl⟩⟩ ⟨_, hx⟩
  obtain rfl := hζ.unique hlam hσ1
  refine ⟨R, Rd, hR, ?_,
    normalizedFunctionalEquation_of_gammaFunctionalEquation hq hδ (by simp) hQd hN⟩
  rw [firstDualFunction_coefficient,
    secondDualFunction_inverseSphericalWhittaker hψ hϖ q hψ' x] at hRd
  exact hRd

end Langlands.Conductor.SphericalCorankOne
