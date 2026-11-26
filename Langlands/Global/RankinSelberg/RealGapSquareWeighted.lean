import Langlands.Global.RankinSelberg.RealGapSquareReflection
import Langlands.Global.RankinSelberg.RealWeightedKernelReflection
import Langlands.Representation.GodementJacquet.InverseTransposeMatrixIntegral

/-! # The scaled determinant identity for a fixed real square coefficient -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapSquareWeighted

open ArchimedeanLocal
open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose)
open ArchimedeanMellinPair (theta)
open RealGodement (realRectangularSchwartzFourier)
open RealJacquet (realAdjacentMatrixWeight HasRealPairNormalizedGrowth)
open RealGapSquareReflection (realGapSquareReflection)
open RealWeightedKernelReflection (ordinaryWeight reflectedWeight realWeightedKernelReflection)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable (t : ℕ)
local notation "H" => Langlands.GeneralLinear (t + 1) ℝ
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "O" => Matrix.unitaryGroup (Fin (t + 1)) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "ι" => inverseTranspose (t + 1) ℝ

private theorem detPower_eq_cpow (y : H) (s : ℂ) : P y s = (δ y : ℂ) ^ s := by
  have hy : |y.val.det| ≠ 0 := abs_ne_zero.mpr y.det_ne_zero
  change Complex.exp (s * (Real.log |y.val.det| : ℂ)) = ((|y.val.det| : ℝ) : ℂ) ^ s
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy), ← Complex.ofReal_log (abs_nonneg _),
    mul_comm]

private theorem matrixWeight_spectral (η : ℝˣ →* ℂˣ) (Φ : M → ℂ) (s : ℂ) (y : H) :
    realAdjacentMatrixWeight η Φ s y = realAdjacentMatrixWeight η Φ 0 y * (δ y : ℂ) ^ s := by
  unfold realAdjacentMatrixWeight
  rw [zero_add, ← detPower_eq_cpow, add_comm s, show P y ((t : ℂ) / 2 + s) = P y ((t : ℂ) / 2) * P y s by
    simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]]
  ring

/-- Square reflection with a positive scaling of the determinant weight and with the
inverse-transpose change on the dual integrating variable already applied. -/
def RealGapSquareWeightedStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (c : RealCharacterData) (fs : List RealCharacterData),
    fs.length = t + 1 →
  ∀ (Φ : 𝓢(M, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : O => fun X : M =>
      Φ ((((Unitary.toUnits k : H))⁻¹).val * X))) →
  ∀ (B : Automorphic.realStandardKFinite (t + 1) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) a B →
  ∀ (f : Automorphic.realStandardKFinite (t + 1) (fs.map RealBlock.character)) (x : H)
    (rate L : ℝ), 0 < rate → ∀ (b : ℝ), 0 < b →
    let w := ordinaryWeight [RealBlock.character c] (fs.map RealBlock.character) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1 rate L
    let wd := reflectedWeight ([RealBlock.character c].map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) rate L
    (∫ y, realAdjacentMatrixWeight c.character.toMonoidHom Φ 0 y * B f (x * y) * w (b * δ y)
        ∂D.groupHaar) =
      (b : ℂ) * ∫ y, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a Φ) 0 (ι y) * B f (x * y) * wd (b⁻¹ * δ (ι y)) ∂D.groupHaar

set_option maxHeartbeats 800000 in
theorem realGapSquareWeighted : RealGapSquareWeightedStatement t := by
  intro D a c fs hfs Φ hΦ B hB f x rate L hrate b hb
  dsimp only
  let μ := D.groupHaar
  have : μ.IsHaarMeasure := D.groupHaar_isHaar
  let F (y : H) := B f (x * y)
  let Fd (y : H) := F (ι y)
  let Φd := realRectangularSchwartzFourier a Φ
  let K (s : ℂ) (y : H) := realAdjacentMatrixWeight c.character.toMonoidHom Φ s y * F y
  let Kd (s : ℂ) (y : H) := realAdjacentMatrixWeight c.inverse.character.toMonoidHom Φd s y * Fd y
  obtain ⟨hConv, hN⟩ := realGapSquareReflection t D a c fs hfs Φ hΦ B hB f x
  have hm : Measurable (δ : H → ℝ) := (Units.continuous_val.matrix_det.abs).measurable
  have hp (y : H) : 0 < δ y := abs_pos.mpr y.det_ne_zero
  have hK (s : ℂ) (y : H) : K s y = K 0 y * (δ y : ℂ) ^ s := by
    simp only [K, matrixWeight_spectral t _ Φ s y]
    ring
  have hKd (s : ℂ) (y : H) : Kd s y = Kd 0 y * (δ y : ℂ) ^ s := by
    simp only [Kd, matrixWeight_spectral t _ Φd s y]
    ring
  have hE := realWeightedKernelReflection μ μ K Kd δ δ hm hm hp hp hK hKd hConv
    [RealBlock.character c] (fs.map RealBlock.character)
    ([RealBlock.character c].map RealLocalJacquet.dualBlock)
    ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
    (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1 hN rate L hrate hb
  unfold theta at hE
  change (∫ y, K 0 y * _ ∂μ) = _
  rw [hE]
  have hι : MeasurePreserving ι μ μ := Langlands.GodementJacquet.realHaar_measurePreserving_inverseTranspose (t + 1) μ
  rw [← hι.integral_comp (Langlands.GodementJacquet.inverseTransposeMeasurableEquiv hι.measurable).measurableEmbedding]
  congr 1

end Langlands.Global.RankinSelbergGlobal.RealGapSquareWeighted
