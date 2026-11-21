import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Representation.Archimedean.TransposeHaar
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionConvergence

/-! # The continued Godement value and the complex quotient recursion -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter

open Langlands.Archimedean (characterOfParams characterOfParams_exponent characterOfParams_weight)
open Langlands.GeneralLinear (determinant)
open Langlands.GodementJacquet
open Langlands.HarmonicAnalysis (partialFourierPlusIntegral_join unipotentFourierSum)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodement (characterWeight)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementWhittaker (augmentedPoint kernelBase)
open ComplexLocalConvergence (HasSimpleRootLogBound)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure ComplexQuotientMeasureData)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Langlands.GeneralLinear.upperUnipotent m ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2

private theorem characterWeight_detWeight (d : ComplexCharacterData) {j : ℕ}
    (g : Langlands.GeneralLinear j ℂ) (t : ℂ) :
    characterWeight d t (determinant g) =
      complexJacquetDetWeight d.character.toMonoidHom g t := by
  change (d.character (determinant g) : ℂ) * ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ t =
    (d.character (determinant g) : ℂ) * Complex.exp (t * Real.log (complexNormalizedAbs g.val.det))
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (complexNormalizedAbs_det_pos g).ne'),
    ← Complex.ofReal_log (complexNormalizedAbs_det_pos g).le, mul_comm _ t]

private theorem shifted_detWeight (d : ComplexCharacterData) {j : ℕ}
    (g : Langlands.GeneralLinear j ℂ) (s t : ℂ) :
    complexJacquetDetWeight (characterOfParams d.weight (d.exponent + s)).character.toMonoidHom g t =
      complexJacquetDetWeight d.character.toMonoidHom g (t + s) := by
  let z := determinant g
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hne : (‖(z : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hpower : ArchimedeanLocal.detPower complexNormalizedAbs g s = (‖(z : ℂ)‖ : ℂ) ^ (2 * s) := by
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hz.le]
    change Complex.exp (s * (Real.log (‖(z : ℂ)‖ ^ 2) : ℂ)) =
      Complex.exp ((Real.log ‖(z : ℂ)‖ : ℂ) * (2 * s))
    rw [Real.log_pow]
    congr 1
    push_cast
    ring
  rw [complexJacquetDetWeight_add, hpower]
  change ((characterOfParams d.weight (d.exponent + s)).character z : ℂ) * _ =
    ((d.character z : ℂ) * _) * _
  rw [(characterOfParams d.weight (d.exponent + s)).character_eq, d.character_eq]
  simp only [characterOfParams_exponent, characterOfParams_weight, mul_add, Complex.cpow_add _ _ hne]
  ring

private theorem partialSchwartz_augmentedPoint (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (g : G) (h : H) :
    partialSchwartz a (complexSelfDualMeasure a) (rightTest g Φ) (augmentedPoint h) =
      complexLastColumnFourier a (fun X => Φ (X * g.val)) h.val
        (Langlands.RankinSelberg.lastRow (h⁻¹)) := by
  rw [partialSchwartz_apply]
  exact partialFourierPlusIntegral_join (complexScaledCharacter a) (complexSelfDualMeasure a)
    (rightTest g Φ) h.val (Langlands.RankinSelberg.lastRow (h⁻¹))

/-- The two forms of Jacquet's recursion agree at every added exponent. The
lower-rank coefficient has character `-a` and the column Fourier phase is `a`. -/
theorem continuedValue_eq_signed_recursion (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) {W : H → ℂ} (hWc : Continuous W)
    (hU : ∀ (u : U) (k : H), W (u.val * k) = traceCharacter (-a) (unipotentFourierSum r u) * W k)
    (hW : HasSimpleRootLogBound W) (g : G) (s : ℂ) :
    continuedValue D.groupHaar (complexSelfDualMeasure a) d a Φ W g s =
      (d.character ((-1 : ℂˣ) ^ m) : ℂ) *
        complexJacquetRecursion (-a) D Φ W
          (characterOfParams d.weight (d.exponent + s)).character.toMonoidHom g := by
  let t := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := t.locallyCompactSpace
  let : SecondCountableTopology H := t.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.groupHaar
  let : D.groupHaar.IsMulRightInvariant := Archimedean.isMulRightInvariant_archimedeanGL ℂ m D.groupHaar
  let : D.groupHaar.IsInvInvariant := Unfolding.isInvInvariant_of_isMulRightInvariant D.groupHaar
  let μ := complexSelfDualMeasure a
  let d' := characterOfParams d.weight (d.exponent + s)
  let S : ℂ := d.character ((-1 : ℂˣ) ^ m)
  let C := complexJacquetDetWeight d'.character.toMonoidHom g sm
  let X := rightTest g Φ
  let J := complexJacquetRecursionGroupKernel (-a) Φ W d'.character.toMonoidHom g
  let K := iteratedKernel (complexScaledCharacter a) μ d X W ((((m : ℕ) + 1 : ℂ) / 2) + s)
  have h_exp : ((((m : ℕ) + 1 : ℂ) / 2) + s) - 1 = (sn - 1) + s := by push_cast; ring
  have hK (h : H) : C * K h = J h⁻¹ := by
    dsimp only [K, J]
    rw [iteratedKernel_eq _ _ _ _ (partialSchwartz a μ X) (partialSchwartz_apply a μ X),
      kernelBase, h_exp, partialSchwartz_augmentedPoint a Φ g h]
    simp only [complexJacquetRecursionGroupKernel, inv_inv, neg_neg]
    change C * (_ * W h⁻¹ * (d.character (determinant h) : ℂ) *
      ArchimedeanLocal.detPower complexNormalizedAbs h ((sn - 1) + s)) =
      C * _ * W h⁻¹ * complexJacquetDetWeight d'.character.toMonoidHom h (sn - 1)
    have hWeight : complexJacquetDetWeight d.character.toMonoidHom h ((sn - 1) + s) =
        (d.character (determinant h) : ℂ) *
          ArchimedeanLocal.detPower complexNormalizedAbs h ((sn - 1) + s) := rfl
    rw [shifted_detWeight d h s (sn - 1), hWeight]
    simp only [mul_assoc]
  change _ = S * complexJacquetRecursion (-a) D Φ W d'.character.toMonoidHom g
  rw [complexJacquetRecursion_eq_group_of_simpleRootLogBound (-a) D Φ d' hWc hU hW g]
  change (S * characterWeight d sm (determinant g)) *
    ArchimedeanLocal.detPower complexNormalizedAbs g s * (∫ h, K h ∂D.groupHaar) =
    S * ∫ k, J k ∂D.groupHaar
  rw [mul_assoc S, characterWeight_detWeight, ← complexJacquetDetWeight_add,
    ← shifted_detWeight d g s sm, mul_assoc S]
  change S * (C * (∫ h, K h ∂D.groupHaar)) = _
  congr 1
  calc
    C * (∫ h, K h ∂D.groupHaar) = ∫ h, C * K h ∂D.groupHaar :=
      (integral_const_mul C K).symm
    _ = ∫ h, J h⁻¹ ∂D.groupHaar := integral_congr_ae (ae_of_all _ hK)
    _ = ∫ h, J h ∂D.groupHaar := integral_inv_eq_self J D.groupHaar

/-- Compatibility of the continued Godement value with the quotient recursion. -/
def ComplexGodementRecursionComparisonStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ) (D : ComplexQuotientMeasureData r) (d : ComplexCharacterData)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin ((r + 1) + 1)) ℂ, ℂ))
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ), Continuous W →
    (∀ (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ)
      (k : Langlands.GeneralLinear (r + 1) ℂ),
      W (u.val * k) = traceCharacter (-a) (unipotentFourierSum r u) * W k) →
    HasSimpleRootLogBound W →
    ∀ (g : Langlands.GeneralLinear ((r + 1) + 1) ℂ) (s : ℂ),
      continuedValue D.groupHaar (complexSelfDualMeasure a) d a Φ W g s =
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
          complexJacquetRecursion (-a) D Φ W
            (characterOfParams d.weight (d.exponent + s)).character.toMonoidHom g

theorem complexGodementRecursionComparison : ComplexGodementRecursionComparisonStatement :=
  fun _ a D d Φ _ hWc hU hW g s => continuedValue_eq_signed_recursion a D d Φ hWc hU hW g s

end Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter
