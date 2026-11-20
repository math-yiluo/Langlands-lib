import Langlands.Global.RankinSelberg.ComplexLocalEqualSquareFourier
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices

/-! # Removing the mixed Fourier signs in the unfolded complex equal-rank integral -/

noncomputable section

open MeasureTheory
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient unipotent_det)

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "N" => GeneralLinear.upperUnipotent m ℂ
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "Z" => (GeneralLinear.scalar (-1 : ℂˣ) : H)
local notation "pad" => (padGL (R := ℂ) (Nat.le_succ (r + 1)))
local notation "J" => (pad Z)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

private theorem negScalar_sq : Z * Z = (1 : H) := by
  rw [← map_mul]
  simp

private theorem negRows_sq : J * J = (1 : G) := by
  rw [← map_mul, negScalar_sq, map_one]

private theorem determinant_negScalar : GeneralLinear.determinant Z = (-1 : ℂˣ) ^ m := by
  simp

private theorem determinant_negRows : GeneralLinear.determinant J = (-1 : ℂˣ) ^ m := by
  apply Units.ext
  change (pad Z).val.det = _
  rw [UnequalAnalytic.det_padGL]
  exact congrArg Units.val determinant_negScalar

private theorem negRows_val (Y : M) :
    (J : G).val * Y = complexSquareNegateFirstRows Y := by
  have hJ : (J : G).val = Matrix.diagonal (Fin.lastCases 1 (fun _ : Fin m => (-1 : ℂ))) := by
    ext i j
    refine Fin.lastCases ?_ (fun i₀ => ?_) i
    · simp [UnequalAnalytic.padGL_apply, Matrix.diagonal_apply, Matrix.one_apply]
    · refine Fin.lastCases ?_ (fun j₀ => ?_) j
      · simp [UnequalAnalytic.padGL_apply]
      · simp [UnequalAnalytic.padGL_apply, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar, Matrix.diagonal_apply, i₀.isLt, j₀.isLt, Fin.ext_iff]
  rw [hJ]
  ext i j
  rw [Matrix.diagonal_mul]
  refine Fin.lastCases ?_ (fun i₀ => ?_) i <;> simp [complexSquareNegateFirstRows]

private theorem detPower_mul_negScalar (h : H) (s : ℂ) : P (h * Z) s = P h s := by
  have hz : ‖(Z : H).val.det‖ = 1 := by
    change ‖(GeneralLinear.determinant Z : ℂ)‖ = 1
    simp [norm_pow]
  simp only [ArchimedeanLocal.detPower, complexNormalizedAbs, Units.val_mul, Matrix.det_mul,
    norm_mul, hz, mul_one]

private theorem detPower_negRows_mul (g : G) (s : ℂ) : P (J * g) s = P g s := by
  have hJ : ‖(J : G).val.det‖ = 1 := by
    change ‖(GeneralLinear.determinant J : ℂ)‖ = 1
    rw [determinant_negRows]
    simp [norm_pow]
  simp only [ArchimedeanLocal.detPower, complexNormalizedAbs, Units.val_mul, Matrix.det_mul,
    norm_mul, hJ, one_mul]

/-- The smaller quotient kernel of the double integral (8.1). -/
def complexEqualUnfoldedInner (U : H → ℂ) (V : G → ℂ) (g : G) (s : ℂ) (q : Q) : ℂ :=
  U q.out * V (pad q.out * g) * P q.out (s - 1 / 2)

/-- The double integral after unfolding the equal-rank product, with matrix test `Ψ`. -/
def complexEqualUnfoldedIntegral (μ : Measure G) (D : ComplexQuotientMeasureData r)
    (η : ℂˣ →* ℂˣ) (Ψ : M → ℂ) (U : H → ℂ) (V : G → ℂ) (s : ℂ) : ℂ :=
  ∫ g : G, Ψ g.val * (η (GeneralLinear.determinant g) : ℂ) * P g (s + ((m : ℕ) : ℂ) / 2) *
    (∫ q, complexEqualUnfoldedInner U V g s q ∂D.measure) ∂μ

private theorem integral_inner_negRows (D : ComplexQuotientMeasureData r)
    (U : H → ℂ) (V : G → ℂ)
    (hUV : ∀ (g : G) (u : N) (h : H),
      U (u.val * h) * V (pad (u.val * h) * g) = U h * V (pad h * g))
    (c : ℂ) (hU : ∀ h : H, U (h * Z) = c * U h) (g : G) (s : ℂ) :
    (∫ q, complexEqualUnfoldedInner U V (J * g) s q ∂D.measure) =
      c * ∫ q, complexEqualUnfoldedInner U V g s q ∂D.measure := by
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let e := rightTranslate N Z
  have he : MeasurePreserving e D.measure D.measure := D.compatible.right_invariant Z
  rw [← he.integral_comp e.toMeasurableEquiv.measurableEmbedding, ← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun q => ?_
  let h := q.out
  let f (x : H) := U x * V (pad x * (J * g)) * P x (s - 1 / 2)
  have hf (u : N) (x : H) : f (u.val * x) = f x := by
    simp only [f, hUV, ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  have hq : e q = Quotient.mk _ (h * Z) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrep : f (Quotient.mk (QuotientGroup.rightRel N) (h * Z)).out = f (h * Z) :=
    congrArg (descend N f hf) (Quotient.out_eq (Quotient.mk _ (h * Z)))
  change f (e q).out = _
  rw [hq, hrep]
  have hpad : pad (h * Z) * (J * g) = pad h * g := by
    rw [map_mul, mul_assoc, ← mul_assoc J J, negRows_sq, one_mul]
  simp only [f, complexEqualUnfoldedInner, hU, hpad, detPower_mul_negScalar, h, mul_assoc]

variable (r) in
/-- The mixed and positive square tests give the same unfolded dual integral up
to the smaller Whittaker central scalar after accounting for the recursion sign. -/
def ComplexLocalEqualUnfoldedSignStatement : Prop :=
  ∀ (μ : Measure G), μ.IsHaarMeasure →
  ∀ (D : ComplexQuotientMeasureData r) (η : ℂˣ →* ℂˣ) (a : ℂˣ)
    (Φ : Rect → ℂ) (φ : Row → ℂ) (U : H → ℂ) (V : G → ℂ) (c : ℂ),
    (∀ (g : G) (u : N) (h : H),
      U (u.val * h) * V (pad (u.val * h) * g) = U h * V (pad h * g)) →
    (∀ h : H, U (h * Z) = c * U h) →
    ∀ s : ℂ,
      (η (-1) : ℂ) ^ m * complexEqualUnfoldedIntegral μ D η
        (fun Y => rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure (-a))
          Φ (complexSquareFirstRows Y) * complexFourierTransform a φ (Y (Fin.last m))) U V s =
        c * complexEqualUnfoldedIntegral μ D η
          (rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
            (complexSquareProductTest Φ φ)) U V s

theorem complexLocalEqualUnfoldedSign : ComplexLocalEqualUnfoldedSignStatement r := by
  intro μ hμ D η a Φ φ U V c hUV hU s
  let : μ.IsHaarMeasure := hμ
  let Ψ : M → ℂ := rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
    (complexSquareProductTest Φ φ)
  have htest : (fun Y : M =>
      rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure (-a))
        Φ (complexSquareFirstRows Y) * complexFourierTransform a φ (Y (Fin.last m))) =
      fun Y => Ψ (complexSquareNegateFirstRows Y) :=
    funext (complexLocalEqualMixedFourier a Φ φ)
  rw [htest]
  let F (g : G) := Ψ (complexSquareNegateFirstRows g.val) *
    (η (GeneralLinear.determinant g) : ℂ) * P g (s + ((m : ℕ) : ℂ) / 2) *
    (∫ q, complexEqualUnfoldedInner U V g s q ∂D.measure)
  let Fpos (g : G) := Ψ g.val * (η (GeneralLinear.determinant g) : ℂ) * P g (s + ((m : ℕ) : ℂ) / 2) *
    (∫ q, complexEqualUnfoldedInner U V g s q ∂D.measure)
  let b : ℂ := (η (-1) : ℂ) ^ m
  have hf (g : G) : F (J * g) = (b * c) * Fpos g := by
    have hJg : complexSquareNegateFirstRows (J * g).val = g.val := by
      rw [← negRows_val, ← Units.val_mul, ← mul_assoc, negRows_sq, one_mul]
    have hχ : (η (GeneralLinear.determinant (J * g)) : ℂ) =
        b * (η (GeneralLinear.determinant g) : ℂ) := by
      simp only [b, map_mul, determinant_negRows, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    simp only [F, Fpos, hJg, hχ, detPower_negRows_mul, integral_inner_negRows D U V hUV c hU]
    ring
  have hη : (η (-1) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    simp [pow_two]
  have hb : b ^ 2 = 1 := by
    dsimp only [b]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hη, one_pow]
  change b * (∫ g, F g ∂μ) = c * ∫ g, Fpos g ∂μ
  rw [← integral_mul_left_eq_self F J]
  simp_rw [hf, integral_const_mul]
  rw [← mul_assoc, ← mul_assoc, ← pow_two, hb, one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
