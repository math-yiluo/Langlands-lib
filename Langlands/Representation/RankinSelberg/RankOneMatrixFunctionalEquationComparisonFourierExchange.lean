import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual bilinear exchange for the supplied plus-sign rectangular Fourier integral. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

open MeasureTheory
open scoped BigOperators

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {r s : ℕ}

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K] in
/-- The actual entry pairing is symmetric, without a conjugation or a sign. -/
theorem rectangularPairing_comm (X Y : Matrix (Fin r) (Fin s) K) :
    rectangularPairing X Y = rectangularPairing Y X := by
  simp only [rectangularPairing, mul_comm]

/-- The actual two-test kernel for the plus rectangular Fourier integral. -/
def rectangularFourierExchangeKernel (ψ : UnitaryAdditiveCharacter K)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
    (z : Matrix (Fin r) (Fin s) K × Matrix (Fin r) (Fin s) K) : ℂ :=
  Φ z.1 * Ψ z.2 * ψ.complex (rectangularPairing z.1 z.2)

/-- The supplied plus Fourier integral is symmetric for the bilinear integral
pairing on actual rectangular Schwartz tests. Both scalar products are integrable. -/
theorem rectangularFourierIntegral_exchange
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure]
    (Φ Ψ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) :
    Integrable (fun X => rectangularFourierIntegral ψ ν Φ X * Ψ X)
      (RankinSelberg.rectangularMeasure ν r s) ∧
    Integrable (fun X => Φ X * rectangularFourierIntegral ψ ν Ψ X)
      (RankinSelberg.rectangularMeasure ν r s) ∧
    (∫ X, rectangularFourierIntegral ψ ν Φ X * Ψ X
      ∂RankinSelberg.rectangularMeasure ν r s) =
      ∫ X, Φ X * rectangularFourierIntegral ψ ν Ψ X
        ∂RankinSelberg.rectangularMeasure ν r s := by
  let : SecondCountableTopology (Matrix (Fin r) (Fin s) K) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin s → K))
  let μ := RankinSelberg.rectangularMeasure ν r s
  let k := rectangularFourierExchangeKernel ψ Φ Ψ
  have hΦ : Integrable Φ μ :=
    Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
  have hΨ : Integrable Ψ μ :=
    Ψ.continuous.integrable_of_hasCompactSupport Ψ.hasCompactSupport
  have hkcont : Continuous k := by
    apply (Φ.continuous.comp continuous_fst |>.mul
      (Ψ.continuous.comp continuous_snd)).mul
    apply ψ.continuous_complex.comp
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_fst.matrix_elem i j).mul (continuous_snd.matrix_elem i j))
  have hk : Integrable k (μ.prod μ) := by
    apply (hΦ.mul_prod hΨ).mono hkcont.aestronglyMeasurable
    filter_upwards with z
    simp only [k, rectangularFourierExchangeKernel, norm_mul,
      UnitaryAdditiveCharacter.norm_complex, mul_one, le_refl]
  have hx (X : Matrix (Fin r) (Fin s) K) :
      (∫ Y, k (X, Y) ∂μ) = Φ X * rectangularFourierIntegral ψ ν Ψ X := by
    simp only [k, rectangularFourierExchangeKernel, mul_assoc, rectangularPairing_comm X]
    rw [integral_const_mul]
    rfl
  have hy (Y : Matrix (Fin r) (Fin s) K) :
      (∫ X, k (X, Y) ∂μ) = rectangularFourierIntegral ψ ν Φ Y * Ψ Y := by
    simp only [k, rectangularFourierExchangeKernel]
    simp_rw [mul_right_comm (Φ _) (Ψ Y)]
    rw [integral_mul_const]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hy] using hk.integral_prod_right
  · simpa only [hx] using hk.integral_prod_left
  · simpa only [hx, hy] using
      (integral_integral_swap (f := fun X Y => k (X, Y)) hk).symm

end General

section Padic

/-- Exchange with two actual determinant-norm-one left factors. The Fourier
factor becomes inverse transpose of `A * B⁻¹`, with the same supplied measure. -/
theorem padicRectangularFourierIntegral_exchange_left
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (r s : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : AdditiveHaarMeasure F.Carrier)
      (A B : GeneralLinear r F.Carrier),
      T.determinantNorm r A = 1 → T.determinantNorm r B = 1 →
      ∀ (Φ Ψ : SchwartzBruhat (Matrix (Fin r) (Fin s) F.Carrier)),
    Integrable (fun X => rectangularFourierIntegral ψ ν Φ (B.val * X) *
      Ψ (A.val * X)) (RankinSelberg.rectangularMeasure ν r s) ∧
    Integrable (fun X => Φ X * rectangularFourierIntegral ψ ν Ψ
      ((GeneralLinear.inverseTranspose r F.Carrier (A * B⁻¹)).val * X))
      (RankinSelberg.rectangularMeasure ν r s) ∧
    (∫ X, rectangularFourierIntegral ψ ν Φ (B.val * X) * Ψ (A.val * X)
      ∂RankinSelberg.rectangularMeasure ν r s) =
    ∫ X, Φ X * rectangularFourierIntegral ψ ν Ψ
      ((GeneralLinear.inverseTranspose r F.Carrier (A * B⁻¹)).val * X)
      ∂RankinSelberg.rectangularMeasure ν r s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν A B hA hB Φ Ψ
  let μ := RankinSelberg.rectangularMeasure ν r s
  let D := A * B⁻¹
  let ΨD := rectangularLeftRightTranslate D 1 Ψ
  have hD : T.determinantNorm r D = 1 := by
    simp only [D, map_mul, map_inv, hA, hB, inv_one, mul_one]
  have hFourier (X : Matrix (Fin r) (Fin s) F.Carrier) :
      rectangularFourierIntegral ψ ν ΨD X =
        rectangularFourierIntegral ψ ν Ψ
          ((GeneralLinear.inverseTranspose r F.Carrier D).val * X) := by
    change rectangularFourierIntegral ψ ν
      (fun Y => Ψ (D.val * Y * (1 : GeneralLinear s F.Carrier).val)) X = _
    simpa only [Units.val_one, Matrix.mul_one, map_one] using
      padicRectangularFourierIntegral_leftRight F T r s ψ ν D 1 hD (map_one _) Ψ X
  obtain ⟨hl, hr, he⟩ := rectangularFourierIntegral_exchange ψ ν Φ ΨD
  have hp := padicRectangularLeftRight_measurePreserving F T r s μ B 1 hB (map_one _)
  have hi := hp.integrable_comp_of_integrable hl
  let e := rectangularLeftRightHomeomorph B (1 : GeneralLinear s F.Carrier)
  have heq := hp.integral_comp e.measurableEmbedding
    (fun X => rectangularFourierIntegral ψ ν Φ X * ΨD X)
  have hDB (X : Matrix (Fin r) (Fin s) F.Carrier) :
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

end Langlands.HarmonicAnalysis
