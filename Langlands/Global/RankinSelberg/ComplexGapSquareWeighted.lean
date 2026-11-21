import Langlands.Global.RankinSelberg.ComplexGapSquareReflection
import Langlands.Global.RankinSelberg.ComplexGapSeparatedKernels
import Langlands.Global.RankinSelberg.ComplexWeightedKernelReflection

/-! # The scaled determinant identity for a fixed square coefficient -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSquareWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar matrixLebesgue)
open Langlands.Automorphic (complexStandardKFinite)
open Langlands.GeneralLinear (determinant inverseTranspose)
open Langlands.GodementJacquet (complexMatrixHaar_measurePreserving_inverseTranspose inverseTransposeMeasurableEquiv)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexNormalizedAbs)
open ArchimedeanMellinPair (theta)
open ComplexAdjacentUnfolding (splitSquareTransform)
open ComplexGapSeparatedKernels (detPower_add)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (complexGapSquareReflection)
open ComplexGodement (characterWeight normPower)
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexWeightedKernelReflection (ordinaryWeight reflectedWeight complexWeightedKernelReflection)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable (t : ℕ)
local notation "Small" => t + 1
local notation "H" => Langlands.GeneralLinear Small ℂ
local notation "KU" => unitaryCompact ℂ Small
local notation "Square" => Matrix (Fin Small) (Fin Small) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "ι" => inverseTranspose Small ℂ
local notation "ν" => complexGeneralLinearHaar Small

private theorem squareKernel_spectral (d : ComplexCharacterData) (Φ : Square → ℂ)
    (f : H → ℂ) (s : ℂ) (h : H) :
    squareKernel d Φ f s h = squareKernel d Φ f 0 h * (δ h : ℂ) ^ s := by
  let σ := (t : ℂ) / 2
  have hχ : characterWeight d (σ + s) (determinant h) = characterWeight d σ (determinant h) * (δ h : ℂ) ^ s := by
    change (d.character (determinant h) : ℂ) * normPower (σ + s) (determinant h) =
      (d.character (determinant h) : ℂ) * normPower σ (determinant h) * (δ h : ℂ) ^ s
    have hp : (δ h : ℂ) ^ s = P h s := normPower_determinant h s
    rw [normPower_determinant, normPower_determinant, detPower_add, hp, mul_assoc]
  unfold squareKernel
  rw [add_zero, hχ]
  ring

/-- Square reflection with a positive scaling of the determinant weight and with the
inverse-transpose change on the dual integrating variable already applied. -/
def ComplexGapSquareWeightedStatement : Prop :=
  ∀ (a : ℂˣ) (d : ComplexCharacterData) (es : List ComplexCharacterData), es.length = Small →
    ∀ (Φ : 𝓢(Square, ℂ)),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : KU => fun X => Φ (u.val⁻¹.val * X))) →
    ∀ (B : complexStandardKFinite Small es →ₗ[ℂ] (H → ℂ)), IsComplexWhittakerIntertwiner t es a B →
    ∀ (f : complexStandardKFinite Small es) (x : H) (rate L : ℝ), 0 < rate →
    ∀ (b : ℝ), 0 < b →
      let w := ordinaryWeight [d] es a 1 rate L
      let wd := reflectedWeight [d] es rate L
      (∫ y : H, squareKernel d Φ (fun z => B f (x * z)) 0 y * w (b * δ y) ∂ν) =
        (b : ℂ) * ∫ y : H, squareKernel d.inv (splitSquareTransform a Φ) (fun _ => 1) 0 (ι y) *
          B f (x * y) * wd (b⁻¹ * δ (ι y)) ∂ν

set_option maxHeartbeats 800000 in
theorem complexGapSquareWeighted : ComplexGapSquareWeightedStatement t := by
  intro a d es hes Φ hΦ B hB f x rate L hrate b hb
  dsimp only
  let F (y : H) := B f (x * y)
  let Fd (y : H) := F (ι y)
  let Φd := splitSquareTransform a Φ
  let Z := squareKernel d Φ F
  let Zd := squareKernel d.inv Φd Fd
  let w := ordinaryWeight [d] es a 1 rate L
  let wd := reflectedWeight [d] es rate L
  let : CompactSpace KU := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact Small
  let κ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts KU)
  let : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let : IsFiniteMeasure κ := inferInstance
  obtain ⟨hConv, hN⟩ := complexGapSquareReflection t ν κ a d es hes Φ hΦ B hB f x
  have hm : Measurable (δ : H → ℝ) := ((Units.continuous_val.matrix_det.norm).pow 2).measurable
  have hp (y : H) : 0 < δ y := pow_pos (norm_pos_iff.mpr y.det_ne_zero) _
  have hE := complexWeightedKernelReflection ν ν Z Zd δ δ hm hm hp hp
    (squareKernel_spectral t d Φ F) (squareKernel_spectral t d.inv Φd Fd) hConv [d] es a 1 hN rate L hrate hb
  change (∫ y : H, Z 0 y * w (b * δ y) ∂ν) = _
  rw [show (∫ y : H, Z 0 y * w (b * δ y) ∂ν) = (b : ℂ) * ∫ y : H, Zd 0 y * wd (b⁻¹ * δ y) ∂ν from hE]
  have hι : MeasurePreserving ι ν ν := complexMatrixHaar_measurePreserving_inverseTranspose Small (matrixLebesgue Small)
  rw [← hι.integral_comp (inverseTransposeMeasurableEquiv hι.measurable).measurableEmbedding
    (fun y : H => Zd 0 y * wd (b⁻¹ * δ y))]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ fun y => ?_
  simp only [Zd, Fd, F, squareKernel, Langlands.GeneralLinear.inverseTranspose_involutive,
    mul_one, Φd, wd]

end Langlands.Global.RankinSelbergGlobal.ComplexGapSquareWeighted
