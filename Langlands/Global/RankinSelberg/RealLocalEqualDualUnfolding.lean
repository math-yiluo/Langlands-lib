import Langlands.Global.RankinSelberg.RealLocalEqualUnfolding
import Langlands.Global.RankinSelberg.RealGodementColumnReflection

/-! # Real equal-rank unfolding after Weyl and Fourier reflection -/

noncomputable section

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory TopologicalSpace
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal

private local instance (j : ℕ) : MeasurableSpace (Langlands.GeneralLinear (j + 1) ℝ) := borel _
private local instance (j : ℕ) : BorelSpace (Langlands.GeneralLinear (j + 1) ℝ) := ⟨rfl⟩
private local instance (j : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (j + 1) ℝ) := borel _
private local instance (j : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (j + 1) ℝ) := ⟨rfl⟩
private local instance (j : ℕ) : MeasurableSpace (LeftUnipotentQuotient j ℝ) := borel _
private local instance (j : ℕ) : BorelSpace (LeftUnipotentQuotient j ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "n" => (t + 2)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "Q'" => LeftUnipotentQuotient (t + 1) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "C(" d ")" => ((RealCharacterData.character d (-1) : ℂ) ^ (t + 1))

private theorem inverse_character_neg_one (d : RealCharacterData) :
    d.inverse.character (-1) = d.character (-1) := by
  change (d.character (-1))⁻¹ = d.character (-1)
  rw [← map_inv]
  simp

/-- The dual of the normalized recursive coefficient is the recursion for the
inverse character, opposite parameter and Fourier test, times the Weyl sign. -/
theorem dual_equalRecursiveCoefficient (b : ℝˣ) (D : RealQuotientMeasureData t) (Φ : 𝓢(X, ℂ))
    (W : G → ℂ) (hW : KernelWhittakerLaw b W) (d : RealCharacterData) (g : H) :
    ArchimedeanLocal.dualFunction n (equalRecursiveCoefficient b D Φ W hW d) g =
      C(d) * equalRecursiveCoefficient (-b) D (realRectangularSchwartzFourier b Φ)
        (ArchimedeanLocal.dualFunction m W) hW.dual d.inverse g := by
  have hpow : (d.character ((-1 : ℝˣ) ^ m) : ℂ) = C(d) := by
    rw [map_pow, Units.val_pow_eq_pow_val]
  have href := (realGodementQuotientReflection t b d D Φ W hW (weylLong n ℝ * g)).2
  simp only [weylInverseTranspose_apply, map_mul, inverseTranspose_weylLong, ← mul_assoc,
    weylLong_mul_self, one_mul, hpow] at href
  simp only [ArchimedeanLocal.dualFunction, equalRecursiveCoefficient, ← mul_assoc (weylLong n ℝ),
    weylLong_mul_self, one_mul, inverse_character_neg_one]
  rw [href]

variable (t) in
/-- The actual dual equal-rank integral unfolds to the kernel with Fourier tests
and dual coefficients, assuming joint absolute integrability on the dual side.
The upper measure scale is unchanged and the determinant sign is explicit. -/
def RealLocalEqualDualUnfoldingStatement : Prop :=
  ∀ (b : ℝˣ) (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1))
    (scale : ℝ≥0), 0 < scale → D'.unipotentHaar = scale • upperStepHaar (t + 1) b →
  ∀ (Φ : 𝓢(X, ℂ)) (φ : (Fin n → ℝ) → ℂ) (W : G → ℂ) (hW : KernelWhittakerLaw b W)
    (V : H → ℂ) (d : RealCharacterData) (s : ℂ), KernelWhittakerLaw (-b) V →
    let R := equalRecursiveCoefficient b D Φ W hW d
    let V' := ArchimedeanLocal.dualFunction n V
    let φ' := realFourierTransform b φ
    let J := equalUnfoldedKernel d.inverse (equalSquareTest (realRectangularSchwartzFourier b Φ) φ')
      (ArchimedeanLocal.dualFunction m W) V' s
    Integrable J (D.measure.prod D'.groupHaar) →
    Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction n R) V' φ' s) D'.measure ∧
      (scale : ℂ) * realEqualDualIntegral b D' R V φ s =
        C(d) * ∫ p, J p ∂(D.measure.prod D'.groupHaar)

theorem realLocalEqualDualUnfolding : RealLocalEqualDualUnfoldingStatement t := by
  intro b D D' scale hscale hμ Φ φ W hW V d s hV R V' φ' J hJ
  let R' := equalRecursiveCoefficient (-b) D (realRectangularSchwartzFourier b Φ)
    (ArchimedeanLocal.dualFunction m W) hW.dual d.inverse
  let I' := realEqualIntegrand R' V' φ' s
  let I := realEqualIntegrand (ArchimedeanLocal.dualFunction n R) V' φ' s
  have hVi : KernelWhittakerLaw (-(-b)) V' := hV.dual
  obtain ⟨hI', he⟩ := realLocalEqualUnfolding (-b) D D' scale hscale
    (by rw [upperStepHaar_neg]; exact hμ) (realRectangularSchwartzFourier b Φ) φ'
    (ArchimedeanLocal.dualFunction m W) hW.dual V' d.inverse s hVi hJ
  have hi : I = fun q : Q' => C(d) * I' q := by
    funext q
    simp only [I, I', realEqualIntegrand, equalIntegrand, R,
      dual_equalRecursiveCoefficient, R', mul_assoc]
  refine ⟨?_, ?_⟩
  · change Integrable I D'.measure
    rw [hi]
    exact (show Integrable I' D'.measure from hI').const_mul _
  · change (scale : ℂ) * (∫ q, I q ∂D'.measure) = _
    rw [hi, integral_const_mul, mul_left_comm]
    exact congrArg (C(d) * ·) he

end Langlands.Global.RankinSelbergGlobal.RealGodement
