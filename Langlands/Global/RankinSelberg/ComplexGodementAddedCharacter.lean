import Langlands.Global.RankinSelberg.ComplexGodementChamberComparison
import Langlands.Global.RankinSelberg.ComplexGodementPartialFourier
import Langlands.Global.RankinSelberg.ComplexJacquetChamberIntertwiner
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Continuing the complex Godement Whittaker value in the added exponent -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter

open Langlands.Archimedean (characterOfParams)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodement (HasFullRowRank godementSection characterWeight normPower)
open ComplexGodementChamberComparison (complexGodementChamberComparison)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexGodementColumnChange (iteratedKernel complexGodementColumnChange)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexJacquetChamberIntertwiner (openCellIntegral_mem_complexWhittakerModel)
open ComplexJacquetUnipotentMeasure (entryHaar)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ

private def rightEquiv (g : G') : Rect ≃L[ℝ] Rect where
  toFun X := X * g.val
  invFun X := X * g⁻¹.val
  left_inv X := by simp [Matrix.mul_assoc]
  right_inv X := by simp [Matrix.mul_assoc]
  map_add' X Y := Matrix.add_mul X Y g.val
  map_smul' c X := Matrix.smul_mul c X g.val
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

/-- Right translation of a rectangular Schwartz function by the larger group element. -/
def rightTest (g : G') (Φ : 𝓢(Rect, ℂ)) : 𝓢(Rect, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightEquiv g) Φ

@[simp]
theorem rightTest_apply (g : G') (Φ : 𝓢(Rect, ℂ)) (X : Rect) :
    rightTest g Φ X = Φ (X * g.val) := rfl

private theorem shifted_character_apply (d : ComplexCharacterData) (s : ℂ) (z : ℂˣ) :
    ((characterOfParams d.weight (d.exponent + s)).character z : ℂ) =
      (d.character z : ℂ) * normPower s z := by
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hne : (‖(z : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hnorm : normPower s z = (‖(z : ℂ)‖ : ℂ) ^ (2 * s) := by
    change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s = _
    rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hz.le hz.le,
      ← Complex.cpow_add _ _ hne]
    congr 1
    ring
  rw [(characterOfParams d.weight (d.exponent + s)).character_eq, d.character_eq, hnorm]
  change ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ d.weight *
    (‖(z : ℂ)‖ : ℂ) ^ (2 * (d.exponent + s)) = _
  rw [mul_add, Complex.cpow_add _ _ hne, mul_assoc]

private theorem normPower_detPower {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (s : ℂ) :
    normPower s (determinant g) = ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  change ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s = _
  have hp : 0 < complexNormalizedAbs g.val.det := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
  simp only [ArchimedeanLocal.detPower, mul_comm _ s]

private theorem detPower_add {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (x y : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs g (x + y) =
      ArchimedeanLocal.detPower complexNormalizedAbs g x * ArchimedeanLocal.detPower complexNormalizedAbs g y := by
  unfold ArchimedeanLocal.detPower
  rw [add_mul, Complex.exp_add]

private theorem characterWeight_shifted (d : ComplexCharacterData) (s t : ℂ) (g : G') :
    characterWeight (characterOfParams d.weight (d.exponent + s)) t (determinant g) =
      characterWeight d t (determinant g) * ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  change ((characterOfParams d.weight (d.exponent + s)).character (determinant g) : ℂ) *
    normPower t (determinant g) = (d.character (determinant g) : ℂ) * normPower t (determinant g) * _
  rw [shifted_character_apply, normPower_detPower]
  ring

private theorem shifted_character_sign (d : ComplexCharacterData) (s : ℂ) (m : ℕ) :
    ((characterOfParams d.weight (d.exponent + s)).character ((-1 : ℂˣ) ^ m) : ℂ) =
      (d.character ((-1 : ℂˣ) ^ m) : ℂ) := by
  rw [shifted_character_apply, map_pow (normPower s),
    show normPower s (-1 : ℂˣ) = 1 by simp [normPower, normSqC],
    one_pow, mul_one]

private theorem iteratedKernel_shifted (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (s t : ℂ) (Φ : Rect → ℂ) (W : G → ℂ) (h : G) :
    iteratedKernel ψ μ (characterOfParams d.weight (d.exponent + s)) Φ W t h =
      iteratedKernel ψ μ d Φ W (t + s) h := by
  unfold iteratedKernel
  rw [shifted_character_apply, normPower_detPower, detPower_add]
  ring

/-- The entire continuation in the added exponent, evaluated at the given larger group element.
The smaller-rank Whittaker function is held fixed. -/
def continuedValue (ν : Measure G) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (W : G → ℂ) (g : G') (s : ℂ) : ℂ :=
  ((d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
    characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant g)) *
      ArchimedeanLocal.detPower complexNormalizedAbs g s *
        ∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest g Φ) W
          ((((r + 1 : ℕ) + 1 : ℂ) / 2) + s) h ∂ν

private theorem differentiable_continuedValue (ν : Measure G) (hν : ν.IsHaarMeasure)
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (W : complexWhittakerModel r ds (-a)) (g : G') :
    Differentiable ℂ (continuedValue ν μ d a Φ W.val g) := by
  let P := partialSchwartz a μ (rightTest g Φ)
  have hi := (complexGodementColumnChange r ds (-a) ν hν (complexScaledCharacter a) μ d
    (rightTest g Φ) P (partialSchwartz_apply a μ (rightTest g Φ)) W).2
  have hg : Differentiable ℂ (fun s => ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
    unfold ArchimedeanLocal.detPower
    exact (differentiable_id.mul_const _).cexp
  unfold continuedValue
  exact ((differentiable_const _).mul hg).mul (hi.comp ((differentiable_const _).add differentiable_id))

variable (r) in
/-- At fixed smaller-rank chamber data, the added exponent in (7.6) continues to an entire
function of one complex variable for compact full-row-rank Schwartz tests. -/
def ComplexGodementAddedCharacterContinuationStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (ds : List ComplexCharacterData),
    ds.length = r + 1 → IsStrictlyDominant (complexPositionExponent ds) r →
    ∀ (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)), HasCompactSupport (Φ : Rect → ℂ) →
    (∀ X ∈ tsupport (Φ : Rect → ℂ), HasFullRowRank X) →
    ∀ (f : Automorphic.complexStandardKFinite (r + 1) ds) (g : G'),
      let W := openCellIntegral a (entryHaar μ (r + 1)) f.val
      Differentiable ℂ (continuedValue ν μ d a Φ W g) ∧
        ∀ s : ℂ, (complexPositionExponent ds 0).re < (d.exponent + s).re →
          continuedValue ν μ d a Φ W g s =
            openCellIntegral a (entryHaar μ (r + 1 + 1))
              (godementSection ν (characterOfParams d.weight (d.exponent + s)) Φ f.val) g

theorem complexGodementAddedCharacterContinuation : ComplexGodementAddedCharacterContinuationStatement r := by
  intro ν hfin hν hright μ d ds hds he a Φ hcompact hfull f g
  let W := openCellIntegral a (entryHaar μ (r + 1)) f.val
  have hW : W ∈ complexWhittakerModel r ds (-a) := openCellIntegral_mem_complexWhittakerModel μ ds hds a he f
  refine ⟨differentiable_continuedValue ν hν μ d ds a Φ ⟨W, hW⟩ g, ?_⟩
  intro s hs
  let d' := characterOfParams d.weight (d.exponent + s)
  have hdom : IsStrictlyDominant (complexPositionExponent (d' :: ds)) (r + 1) := by
    intro i hi
    cases i with
    | zero => exact hs
    | succ i => exact he i (by omega)
  have hcomp := complexGodementChamberComparison (r := r) ν μ d' ds hdom a Φ Φ.continuous
    hcompact hfull f.val f.2.1 g
  rw [hcomp]
  simp only [d', shifted_character_sign, characterWeight_shifted, iteratedKernel_shifted, continuedValue,
    mul_assoc]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter
