import Langlands.Representation.GodementJacquet.TateScalarMellin
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Conductor.Essential

/-!
# Scalar Tate theory with its principal-unit conductor

This statement uses an arbitrary nonarchimedean local field, the actual scalar
Mellin integrals, and the plus-sign Fourier transform. It asserts no proof.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear Conductor Polynomial
open GeneralLinear.Iwasawa

universe uF

/-- Tate's local scalar theory over every nonarchimedean local field, including
positive characteristic. The natural conductor is characterized directly on the
rank-one principal-unit groups. The two explicit Euler polynomials generate the
actual rational Mellin values, and the functional equation has exactly this
conductor as exponent when the additive character has conductor `O`. -/
def LocalTateConductorStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
    ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ),
      IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      abv (ϖ : F) = (q : ℝ)⁻¹ →
      (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
    ∀ χ : Fˣ →* ℂˣ, Continuous χ →
    ∀ ψ : UnitaryAdditiveCharacter F, HasIntegerConductor ψ →
    ∀ ν : AdditiveHaarMeasure F, IsSelfDual ψ ν →
      ∃ a : ℕ,
        (∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1) ∧
        (∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1) ∧
        ScalarMellinAnalyticData q abv (localMultiplicativeHaar F)
          (fun x => (χ x : ℂ)) 1 ∧
        ScalarMellinAnalyticData q abv (localMultiplicativeHaar F)
          (fun x => ((χ x)⁻¹ : ℂ)) 1 ∧
        let P : ℂ[X] := if a = 0 then 1 - C (χ ϖ : ℂ) * X else 1
        let PDual : ℂ[X] := if a = 0 then 1 - C ((χ ϖ)⁻¹ : ℂ) * X else 1
        IsNormalizedGenerator
          (scalarMellinRationalValues q abv (localMultiplicativeHaar F)
            (fun x => (χ x : ℂ)) 1) P ∧
        IsNormalizedGenerator
          (scalarMellinRationalValues q abv (localMultiplicativeHaar F)
            (fun x => ((χ x)⁻¹ : ℂ)) 1) PDual ∧
        ∃ c : ℂˣ, ∀ Φ : SchwartzBruhat F,
          ∃ Φhat : SchwartzBruhat F,
            (∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
              Φhat y = fourierIntegral ψ ν Φ y) ∧
            ∀ R RDual : RationalFunctions,
              HasRationalContinuation q
                (scalarMellinIntegral abv (localMultiplicativeHaar F)
                  (fun x => (χ x : ℂ)) 1 Φ) R →
              HasRationalContinuation q
                (scalarMellinIntegral abv (localMultiplicativeHaar F)
                  (fun x => ((χ x)⁻¹ : ℂ)) 1 Φhat) RDual →
              NormalizedFunctionalEquation q P PDual 1 c 0 (a : ℤ) R RDual

end Langlands.GodementJacquet
