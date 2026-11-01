import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.Representation.RankinSelberg.CharacterChange

/-! # Actual Weyl substitution for matrix integrals and their rational values -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis RankinSelberg Whittaker

universe uF

section LeftTranslation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ}

/-- Simultaneous left pullback of the test and function is the left pullback
of the actual integrand when the translating determinant has absolute value one. -/
theorem matrixIntegrand_leftTranslate (abv : AbsoluteValue F ℝ)
    (A : GeneralLinear (n + 1) F) (hA : abv (Matrix.det A.val) = 1)
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : GeneralLinear (n + 1) F → ℂ) (g : GeneralLinear (n + 1) F) :
    matrixIntegrand abv (rectangularLeftRightTranslate A 1 Φ) s
        (fun x => f (A * x)) g =
      matrixIntegrand abv Φ s f (A * g) := by
  have hw : determinantWeight abv A s = 1 := by
    simp only [determinantWeight, hA, Complex.ofReal_one, Complex.one_cpow]
  simp only [matrixIntegrand, rectangularLeftRightTranslate_apply, Units.val_one,
    Matrix.mul_one, Units.val_mul, determinantWeight_mul, hw, one_mul]

variable [MeasurableSpace (GeneralLinear (n + 1) F)]
  [BorelSpace (GeneralLinear (n + 1) F)]

/-- Simultaneous norm-one left pullback preserves actual absolute convergence
for every left-invariant group measure. -/
theorem matrixConverges_leftTranslate_iff (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (A : GeneralLinear (n + 1) F) (hA : abv (Matrix.det A.val) = 1)
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : GeneralLinear (n + 1) F → ℂ) :
    MatrixConverges abv μ (rectangularLeftRightTranslate A 1 Φ) s
        (fun x => f (A * x)) ↔
      MatrixConverges abv μ Φ s f := by
  unfold MatrixConverges
  have he : matrixIntegrand abv (rectangularLeftRightTranslate A 1 Φ) s
      (fun x => f (A * x)) = matrixIntegrand abv Φ s f ∘ (fun x => A * x) :=
    funext (matrixIntegrand_leftTranslate abv A hA Φ s f)
  rw [he]
  exact (measurePreserving_mul_left μ A).integrable_comp_emb
    (Homeomorph.mulLeft A).measurableEmbedding

/-- The actual totalized matrix integrals agree after simultaneous norm-one
left pullback, without an integrability assumption. -/
theorem matrixIntegral_leftTranslate (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (A : GeneralLinear (n + 1) F) (hA : abv (Matrix.det A.val) = 1)
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : GeneralLinear (n + 1) F → ℂ) :
    matrixIntegral abv μ (rectangularLeftRightTranslate A 1 Φ) s
        (fun x => f (A * x)) =
      matrixIntegral abv μ Φ s f := by
  unfold matrixIntegral
  simp_rw [matrixIntegrand_leftTranslate abv A hA]
  exact (measurePreserving_mul_left μ A).integral_comp
    (Homeomorph.mulLeft A).measurableEmbedding _

/-- The same right half-plane witnesses shifted convergence on either side. -/
theorem shiftedConvergesOnRight_leftTranslate_iff (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (A : GeneralLinear (n + 1) F) (hA : abv (Matrix.det A.val) = 1)
    (Φ : MatrixTestFunction n F) (f : GeneralLinear (n + 1) F → ℂ) :
    ShiftedConvergesOnRight abv μ (rectangularLeftRightTranslate A 1 Φ)
        (fun x => f (A * x)) ↔
      ShiftedConvergesOnRight abv μ Φ f := by
  unfold ShiftedConvergesOnRight
  simp_rw [matrixConverges_leftTranslate_iff abv μ A hA]

/-- Norm-one left pullback preserves the identical shifted rational value,
including its convergence and reduced-denominator continuation conditions. -/
theorem hasShiftedRationalValue_leftTranslate_iff (q : ℕ)
    (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (A : GeneralLinear (n + 1) F) (hA : abv (Matrix.det A.val) = 1)
    (Φ : MatrixTestFunction n F) (f : GeneralLinear (n + 1) F → ℂ)
    (R : RationalFunctions) :
    HasShiftedRationalValue q abv μ (rectangularLeftRightTranslate A 1 Φ)
        (fun x => f (A * x)) R ↔
      HasShiftedRationalValue q abv μ Φ f R := by
  unfold HasShiftedRationalValue
  simp_rw [shiftedConvergesOnRight_leftTranslate_iff abv μ A hA,
    matrixIntegral_leftTranslate abv μ A hA]

end LeftTranslation

section WeylTranslation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ}

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The unsigned long Weyl determinant has value one under every real absolute
value: its square is one, and absolute values are nonnegative. -/
theorem absoluteValue_det_weylLong (abv : AbsoluteValue F ℝ) (r : ℕ) :
    abv (Matrix.det (GeneralLinear.weylLong r F).val) = 1 := by
  have he : Matrix.det (GeneralLinear.weylLong r F).val *
      Matrix.det (GeneralLinear.weylLong r F).val = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, GeneralLinear.weylLong_mul_self,
      Units.val_one, Matrix.det_one]
  apply (pow_eq_one_iff_of_nonneg (abv.nonneg _) (by decide : 2 ≠ 0)).mp
  rw [pow_two, ← map_mul, he, map_one]

/-- Pullback of full-matrix Schwartz tests by the unsigned long Weyl element. -/
def matrixWeylTranslate (n : ℕ) :
    MatrixTestFunction n F ≃ₗ[ℂ] MatrixTestFunction n F :=
  rectangularLeftRightTranslate (GeneralLinear.weylLong (n + 1) F) 1

@[simp] theorem matrixWeylTranslate_apply (Φ : MatrixTestFunction n F)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    matrixWeylTranslate n Φ X = Φ ((GeneralLinear.weylLong (n + 1) F).val * X) := by
  simp only [matrixWeylTranslate, rectangularLeftRightTranslate_apply, Units.val_one,
    Matrix.mul_one]

/-- The Library's unsigned Whittaker dual is the left Weyl pullback of the
actual inverse-transpose function, rather than a definitional identification. -/
theorem dualFunction_eq_coefficientIota_weyl
    (f : GeneralLinear (n + 1) F → ℂ) :
    dualFunction n f =
      fun g => coefficientIota f (GeneralLinear.weylLong (n + 1) F * g) := by
  funext g
  simp only [dualFunction_apply, coefficientIota, map_mul,
    GeneralLinear.inverseTranspose_weylLong]

variable [MeasurableSpace (GeneralLinear (n + 1) F)]
  [BorelSpace (GeneralLinear (n + 1) F)]

/-- Actual Weyl substitution identifies dual-function convergence with
inverse-transpose convergence for any left-invariant measure. -/
theorem matrixConverges_weylTranslate_dualFunction_iff
    (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : GeneralLinear (n + 1) F → ℂ) :
    MatrixConverges abv μ (matrixWeylTranslate n Φ) s (dualFunction n f) ↔
      MatrixConverges abv μ Φ s (coefficientIota f) := by
  rw [dualFunction_eq_coefficientIota_weyl]
  exact matrixConverges_leftTranslate_iff abv μ _
    (absoluteValue_det_weylLong abv _) Φ s (coefficientIota f)

/-- No extra scalar occurs in the actual Weyl change of variables. -/
theorem matrixIntegral_weylTranslate_dualFunction
    (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : GeneralLinear (n + 1) F → ℂ) :
    matrixIntegral abv μ (matrixWeylTranslate n Φ) s (dualFunction n f) =
      matrixIntegral abv μ Φ s (coefficientIota f) := by
  rw [dualFunction_eq_coefficientIota_weyl]
  exact matrixIntegral_leftTranslate abv μ _
    (absoluteValue_det_weylLong abv _) Φ s (coefficientIota f)

/-- The unsigned Weyl substitution preserves shifted right-half-plane
convergence of the actual dual integral. -/
theorem shiftedConvergesOnRight_weylTranslate_dualFunction_iff
    (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (Φ : MatrixTestFunction n F) (f : GeneralLinear (n + 1) F → ℂ) :
    ShiftedConvergesOnRight abv μ (matrixWeylTranslate n Φ) (dualFunction n f) ↔
      ShiftedConvergesOnRight abv μ Φ (coefficientIota f) := by
  rw [dualFunction_eq_coefficientIota_weyl]
  exact shiftedConvergesOnRight_leftTranslate_iff abv μ _
    (absoluteValue_det_weylLong abv _) Φ (coefficientIota f)

/-- The identical rational function represents either dual integral, with
the same shift and denominator domain. -/
theorem hasShiftedRationalValue_weylTranslate_dualFunction_iff
    (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (Φ : MatrixTestFunction n F) (f : GeneralLinear (n + 1) F → ℂ)
    (R : RationalFunctions) :
    HasShiftedRationalValue q abv μ (matrixWeylTranslate n Φ) (dualFunction n f) R ↔
      HasShiftedRationalValue q abv μ Φ (coefficientIota f) R := by
  rw [dualFunction_eq_coefficientIota_weyl]
  exact hasShiftedRationalValue_leftTranslate_iff q abv μ _
    (absoluteValue_det_weylLong abv _) Φ (coefficientIota f) R

end WeylTranslation

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixComparisonWeylTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance matrixComparisonWeylValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance matrixComparisonWeylLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matrixComparisonWeylGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance matrixComparisonWeylGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- Weyl convergence transport for the actual canonical p-adic matrix integral. -/
theorem matrixConverges_weylTranslate_dualFunction_iff
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : GeneralLinear (n + 1) F.Carrier → ℂ) :
    MatrixConverges F (matrixWeylTranslate n Φ) s (dualFunction n f) ↔
      MatrixConverges F Φ s (coefficientIota f) :=
  GodementJacquet.matrixConverges_weylTranslate_dualFunction_iff
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) Φ s f

/-- The canonical normalized group Haar measure contributes no Weyl scalar. -/
theorem matrixIntegral_weylTranslate_dualFunction
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : GeneralLinear (n + 1) F.Carrier → ℂ) :
    matrixIntegral F (matrixWeylTranslate n Φ) s (dualFunction n f) =
      matrixIntegral F Φ s (coefficientIota f) :=
  GodementJacquet.matrixIntegral_weylTranslate_dualFunction
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) Φ s f

/-- The same shifted right half-plane suffices for the canonical p-adic
dual integral before and after the actual unsigned Weyl substitution. -/
theorem shiftedConvergesOnRight_weylTranslate_dualFunction_iff
    (Φ : MatrixTestFunction n F.Carrier)
    (f : GeneralLinear (n + 1) F.Carrier → ℂ) :
    ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) (matrixWeylTranslate n Φ) (dualFunction n f) ↔
      ShiftedConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ (coefficientIota f) :=
  GodementJacquet.shiftedConvergesOnRight_weylTranslate_dualFunction_iff
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) Φ f

/-- Actual shifted rational values for the canonical p-adic dual integral
are unchanged by the unsigned Weyl substitution. -/
theorem hasShiftedRationalValue_weylTranslate_dualFunction_iff
    (Φ : MatrixTestFunction n F.Carrier)
    (f : GeneralLinear (n + 1) F.Carrier → ℂ) (R : RationalFunctions) :
    HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) (matrixWeylTranslate n Φ) (dualFunction n f) R ↔
      HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier n) Φ (coefficientIota f) R :=
  GodementJacquet.hasShiftedRationalValue_weylTranslate_dualFunction_iff _
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) Φ f R

end Padic

end Langlands.GodementJacquet
