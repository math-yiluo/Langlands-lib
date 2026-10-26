import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# General-field rectangular and block-modulus Haar scaling

Proofs of the published rectangular, block-modulus and aggregate Haar-scaling
propositions over every nonarchimedean local field, including positive
characteristic. The rectangular law specializes the field-generic determinant
change of variables to the published scalar law; the modulus law is the
rectangular law at inverse Levi blocks. Second countability of the field is
derived from the local-field hypotheses by the published scalar proof's helper.
-/

noncomputable section

open scoped NNReal
open MeasureTheory MeasureTheory.Measure

namespace Langlands.HarmonicAnalysis

universe uF

section SecondCountable

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [SecondCountableTopology F]

/-- Scalar Haar scaling implies rectangular Haar scaling, using the published
field-generic determinant change-of-variables theorem. -/
theorem generalRectangularHaarScaling_of_scalar
    (hscalar : GeneralScalarHaarScalingStatement F) :
    GeneralRectangularHaarScalingStatement F := by
  intro q hq abv ϖ hϖ habv hunit r s
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro _ _ μ _ A B
  let χ : F →*₀ ℝ≥0 :=
    { toFun := fun x => ⟨abv x, abv.nonneg x⟩
      map_zero' := Subtype.ext (map_zero abv)
      map_one' := Subtype.ext (map_one abv)
      map_mul' := fun x y => Subtype.ext (map_mul abv x y) }
  have hχ (a : F) (ha : a ≠ 0) :
      (addHaar : Measure F).map (fun x => a * x) = (χ a)⁻¹ • addHaar :=
    hscalar q hq abv ϖ hϖ habv hunit addHaar (Units.mk0 a ha)
  have h := haarMeasure_map_rectangular addHaar χ hχ μ
    (A : Matrix (Fin r) (Fin r) F)
    ((B⁻¹ : GeneralLinear s F) : Matrix (Fin s) (Fin s) F)
    (GeneralLinear.determinant A).ne_zero (GeneralLinear.determinant B⁻¹).ne_zero
  change μ.map _ =
    ((Shahidi.determinantAbs abv r A : ℝ≥0) ^ Fintype.card (Fin s) *
      (Shahidi.determinantAbs abv s B⁻¹ : ℝ≥0) ^ Fintype.card (Fin r))⁻¹ • μ at h
  simpa only [Fintype.card_fin, map_inv, Units.val_inv_eq_inv_val,
    inv_pow, div_eq_mul_inv] using h

/-- The swapped-block modulus is rectangular scaling at inverse Levi blocks. -/
theorem generalModulusScaling_of_rectangular
    (hrect : GeneralRectangularHaarScalingStatement F) :
    GeneralModulusScalingStatement F := by
  intro q hq abv ϖ hϖ habv hunit m n hm hn _ _ _ μ _ l
  let A : GeneralLinear n F := l 0
  let B : GeneralLinear m F := l 1
  have h := hrect q hq abv ϖ hϖ habv hunit n m μ
    A⁻¹ B⁻¹
  rw [inv_inv] at h
  change μ.map (fun X =>
    ((A⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * X *
      (B : Matrix (Fin m) (Fin m) F)) = _
  rw [h, Shahidi.leviModulus_twoBlocks]
  change
    (((Shahidi.determinantAbs abv n A⁻¹ : ℝ≥0) ^ m /
      (Shahidi.determinantAbs abv m B⁻¹ : ℝ≥0) ^ n)⁻¹) • μ =
    (((Shahidi.determinantAbs abv n A) ^ m /
      (Shahidi.determinantAbs abv m B) ^ n : ℝ≥0ˣ) : ℝ≥0) • μ
  congr 1
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_pow, div_eq_mul_inv,
    inv_inv, mul_inv, Units.val_mul, Units.val_pow_eq_pow_val]

end SecondCountable

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The exact published general-field rectangular Haar scaling proposition. -/
theorem generalRectangularHaarScalingStatement :
    GeneralRectangularHaarScalingStatement.{uF} F := by
  have := GeneralLocalField.secondCountableTopology F
  exact generalRectangularHaarScaling_of_scalar F (generalScalarHaarScalingStatement F)

/-- The exact published general-field block-modulus Haar scaling proposition. -/
theorem generalModulusScalingStatement :
    GeneralModulusScalingStatement.{uF} F := by
  have := GeneralLocalField.secondCountableTopology F
  exact generalModulusScaling_of_rectangular F (generalRectangularHaarScalingStatement F)

/-- The exact published aggregate general-field Haar scaling proposition. -/
theorem generalAdditiveHaarScalingStatement :
    GeneralAdditiveHaarScalingStatement.{uF} F :=
  ⟨generalScalarHaarScalingStatement F, generalRectangularHaarScalingStatement F,
    generalModulusScalingStatement F⟩

end Langlands.HarmonicAnalysis
