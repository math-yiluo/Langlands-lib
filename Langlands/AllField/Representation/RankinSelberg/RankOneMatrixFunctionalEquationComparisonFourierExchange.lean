import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierExchange
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
/-! Actual bilinear exchange for the supplied plus-sign rectangular Fourier integral. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

open _root_.MeasureTheory
open scoped BigOperators

universe uK uF

section General


end General

section Padic

/-- Exchange with two actual determinant-norm-one left factors. The Fourier
factor becomes inverse transpose of `A * B⁻¹`, with the same supplied measure. -/
theorem padicRectangularFourierIntegral_exchange_left
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (r s : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F)
      (A B : GeneralLinear r F),
      T.determinantNorm r A = 1 → T.determinantNorm r B = 1 →
      ∀ (Φ Ψ : SchwartzBruhat (Matrix (Fin r) (Fin s) F)),
    Integrable (fun X => rectangularFourierIntegral ψ ν Φ (B.val * X) *
      Ψ (A.val * X)) (RankinSelberg.rectangularMeasure ν r s) ∧
    Integrable (fun X => Φ X * rectangularFourierIntegral ψ ν Ψ
      ((GeneralLinear.inverseTranspose r F (A * B⁻¹)).val * X))
      (RankinSelberg.rectangularMeasure ν r s) ∧
    (∫ X, rectangularFourierIntegral ψ ν Φ (B.val * X) * Ψ (A.val * X)
      ∂RankinSelberg.rectangularMeasure ν r s) =
    ∫ X, Φ X * rectangularFourierIntegral ψ ν Ψ
      ((GeneralLinear.inverseTranspose r F (A * B⁻¹)).val * X)
      ∂RankinSelberg.rectangularMeasure ν r s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν A B hA hB Φ Ψ
  let μ := RankinSelberg.rectangularMeasure ν r s
  let D := A * B⁻¹
  let ΨD := rectangularLeftRightTranslate D 1 Ψ
  have hD : T.determinantNorm r D = 1 := by
    simp only [D, map_mul, map_inv, hA, hB, inv_one, mul_one]
  have hFourier (X : Matrix (Fin r) (Fin s) F) :
      rectangularFourierIntegral ψ ν ΨD X =
        rectangularFourierIntegral ψ ν Ψ
          ((GeneralLinear.inverseTranspose r F D).val * X) := by
    change rectangularFourierIntegral ψ ν
      (fun Y => Ψ (D.val * Y * (1 : GeneralLinear s F).val)) X = _
    simpa only [Units.val_one, Matrix.mul_one, map_one] using
      padicRectangularFourierIntegral_leftRight F T r s ψ ν D 1 hD (map_one _) Ψ X
  obtain ⟨hl, hr, he⟩ := rectangularFourierIntegral_exchange ψ ν Φ ΨD
  have hp := padicRectangularLeftRight_measurePreserving F T r s μ B 1 hB (map_one _)
  have hi := hp.integrable_comp_of_integrable hl
  let e := rectangularLeftRightHomeomorph B (1 : GeneralLinear s F)
  have heq := hp.integral_comp e.measurableEmbedding
    (fun X => rectangularFourierIntegral ψ ν Φ X * ΨD X)
  have hDB (X : Matrix (Fin r) (Fin s) F) :
      ΨD (B.val * X) = Ψ (A.val * X) := by
    simp only [ΨD, rectangularLeftRightTranslate_apply, Units.val_one, Matrix.mul_one, D]
    rw [Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B⁻¹).val B.val X,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Matrix.mul_one, Units.val_one, hDB, Function.comp_def] using hi
  · simpa only [hFourier, D] using hr
  · simp only [Units.val_one, Matrix.mul_one, hDB] at heq
    exact heq.trans (by simpa only [hFourier, D] using he)

end Padic

end Langlands.AllField.HarmonicAnalysis
