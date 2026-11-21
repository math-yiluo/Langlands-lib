import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionWeil
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar

/-! # The continued complex Godement value and the quotient recursion -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter

open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure)
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open ComplexGodement (characterWeight normPower)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementPartialFourier
open ComplexGodementWhittaker (augmentedPoint kernelBase)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => r + 1 + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin m) (Fin m) ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "ν" => complexSelfDualMeasure

private theorem invInvariant_groupHaar (D : ComplexQuotientMeasureData r) :
    D.groupHaar.IsInvInvariant := by
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  let : LocallyCompactSpace Mat := inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℂ))
  let : BorelSpace Mat := inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))
  let μ := Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts Mat))
  let : μ.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  let μH := complexMatrixHaar m μ
  let : μH.IsHaarMeasure := complexMatrixHaar_isHaar m μ
  let : μH.IsMulRightInvariant := complexMatrixHaar_isMulRightInvariant m μ
  let : μH.IsInvInvariant := Unfolding.isInvInvariant_of_isMulRightInvariant μH
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  constructor
  rw [Measure.isMulLeftInvariant_eq_smul D.groupHaar μH, Measure.inv_def,
    Measure.map_smul _ measurable_inv.aemeasurable, Measure.map_inv_eq_self]

private theorem characterWeight_eq_recursionDet {j : ℕ} (d : ComplexCharacterData)
    (g : Langlands.GeneralLinear j ℂ) (s : ℂ) :
    characterWeight d s (determinant g) = complexJacquetDetWeight d.character.toMonoidHom g s := by
  change (d.character (determinant g) : ℂ) * normPower s (determinant g) =
    (d.character (determinant g) : ℂ) * ArchimedeanLocal.detPower complexNormalizedAbs g s
  congr 1
  have h := complexNormalizedAbs_det_pos g
  change (complexNormalizedAbs g.val.det : ℂ) ^ s =
    Complex.exp (s * (Real.log (complexNormalizedAbs g.val.det) : ℂ))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'),
    ← Complex.ofReal_log h.le, mul_comm _ s]

private theorem recursionGroupKernel_inv_eq_iterated (a : ℂˣ) (d : ComplexCharacterData)
    (Φ : 𝓢(Rect, ℂ)) (W : H → ℂ) (g : G) (h : H) :
    complexJacquetRecursionGroupKernel (-a) Φ W d.character.toMonoidHom g h⁻¹ =
      complexJacquetDetWeight d.character.toMonoidHom g ((m : ℕ) / (2 : ℂ)) *
        iteratedKernel (complexScaledCharacter a) (ν a) d (rightTest g Φ) W
          ((n : ℕ) / (2 : ℂ)) h := by
  rw [iteratedKernel_eq (complexScaledCharacter a) (ν a) d (rightTest g Φ)
    (partialSchwartz a (ν a) (rightTest g Φ)) (partialSchwartz_apply a (ν a) _) W, kernelBase,
    partialSchwartz_apply]
  have hFourier :
      complexLastColumnFourier a (fun X => Φ (X * g.val)) h.val (Langlands.RankinSelberg.lastRow h⁻¹) =
        partialFourierPlusIntegral (complexScaledCharacter a) (ν a) (rightTest g Φ)
          (augmentedPoint h) := by
    change _ = partialFourierPlusIntegral (complexScaledCharacter a) (ν a) (rightTest g Φ)
      (rectangularJoin h.val (Langlands.RankinSelberg.lastRow h⁻¹))
    rw [partialFourierPlusIntegral_join]
    rfl
  simp only [complexJacquetRecursionGroupKernel, inv_inv, neg_neg, hFourier,
    complexJacquetDetWeight, ContinuousMonoidHom.coe_toMonoidHom, mul_assoc]
  rfl

/-- At the actual adjoining character, the continued column integral agrees with
the quotient recursion multiplied by the Weyl determinant sign. -/
def ComplexGodementRecursionBridgeStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (a : ℂˣ) (d : ComplexCharacterData)
    (Φ : 𝓢(Rect, ℂ)) (ds : List ComplexCharacterData) (W : complexWhittakerModel r ds (-a)) (g : G),
    continuedValue D.groupHaar (ν a) d a Φ W.val g 0 =
      (d.character ((-1 : ℂˣ) ^ m) : ℂ) *
        complexJacquetRecursion (-a) D Φ W.val d.character.toMonoidHom g

theorem complexGodementRecursionBridge : ComplexGodementRecursionBridgeStatement (r := r) := by
  intro D a d Φ ds W g
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsInvInvariant := invInvariant_groupHaar D
  let f : H → ℂ := iteratedKernel (complexScaledCharacter a) (ν a) d (rightTest g Φ) W.val
    ((n : ℕ) / (2 : ℂ))
  let K := complexJacquetRecursionGroupKernel (-a) Φ W.val d.character.toMonoidHom g
  let c := complexJacquetDetWeight d.character.toMonoidHom g ((m : ℕ) / (2 : ℂ))
  have hf : Integrable f D.groupHaar := by
    simpa only [f, neg_neg] using
      (complexGodementIteratedIntegral r ds (-a) D.groupHaar D.groupHaar_isHaar
        (ν a) d (rightTest g Φ) W).1 ((n : ℕ) / (2 : ℂ))
  have hK (h : H) : K h⁻¹ = c * f h :=
    recursionGroupKernel_inv_eq_iterated a d Φ W.val g h
  have hI : Integrable K D.groupHaar := by
    refine ((hf.const_mul c).comp_inv).congr (ae_of_all _ fun h => ?_)
    simpa only [inv_inv] using (hK h⁻¹).symm
  have hW (u : Langlands.GeneralLinear.upperUnipotent m ℂ) (h : H) :
      W.val (u.val * h) = traceCharacter (-a) (unipotentFourierSum r u) * W.val h :=
    complexWhittakerModel_left_equivariant W.2 u.val u.2 h
  rw [complexJacquetRecursion_eq_integral_group (-a) D Φ W.val _ hW g hI]
  change continuedValue D.groupHaar (ν a) d a Φ W.val g 0 =
    (d.character ((-1 : ℂˣ) ^ m) : ℂ) * ∫ h, K h ∂D.groupHaar
  rw [← integral_inv_eq_self K D.groupHaar]
  simp_rw [hK, integral_const_mul]
  unfold continuedValue
  simp only [add_zero, ArchimedeanLocal.detPower, zero_mul, Complex.exp_zero, mul_one,
    f, c, Nat.cast_add, Nat.cast_one, characterWeight_eq_recursionDet, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter
