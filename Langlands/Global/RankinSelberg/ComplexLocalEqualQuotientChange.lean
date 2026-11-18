import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerChangeCharacter
import Langlands.Global.RankinSelberg.UnipotentConjugationModulus
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # The complex equal-rank quotient under a change of additive character -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange

open ArchimedeanLocal Langlands.LocalFactor.Archimedean Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow_unipotent_mul unipotent_det)
open UnipotentConjugationModulus (conjugation conjugation_apply)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ

private theorem conjugation_changeDiagonal_mem_iff (a : ℂˣ) (g : G) :
    conjugation (changeDiagonal r a) g ∈ N ↔ g ∈ N := by
  let d : Fin (r + 1) → ℂˣ := fun i => a ^ (r - i.val)
  let t := changeDiagonal r a
  rw [conjugation_apply]
  refine ⟨fun h => ?_, diagonal_conj_mem d g⟩
  have h' := diagonal_conj_mem d⁻¹ (t * g * t⁻¹) h
  rw [map_inv, inv_inv] at h'
  change t⁻¹ * (t * g * t⁻¹) * t ∈ N at h'
  rwa [show t⁻¹ * (t * g * t⁻¹) * t = g by group] at h'

private def changeConjugationQuotient (a : ℂˣ) : Q ≃ₜ Q :=
  quotientAutomorphism N (conjugation (changeDiagonal r a))
    (conjugation_changeDiagonal_mem_iff a)

/-- Transport the group, unipotent and quotient measures together by conjugation by the
change-of-character diagonal. -/
def changeQuotientMeasure (a : ℂˣ) (D : ComplexQuotientMeasureData r) :
    ComplexQuotientMeasureData r := by
  let e := conjugation (changeDiagonal r a)
  let eN := subgroupAutomorphism N e (conjugation_changeDiagonal_mem_iff a)
  let eQ := changeConjugationQuotient (r := r) a
  letI := D.groupHaar_isHaar
  letI := D.unipotentHaar_isHaar
  letI := D.unipotentHaar_rightInvariant
  exact
    { groupHaar := Measure.map e D.groupHaar
      groupHaar_isHaar := e.isHaarMeasure_map D.groupHaar
      unipotentHaar := Measure.map eN D.unipotentHaar
      unipotentHaar_isHaar := eN.isHaarMeasure_map D.unipotentHaar
      unipotentHaar_rightInvariant := isMulRightInvariant_map eN D.unipotentHaar
      measure := Measure.map eQ D.measure
      compatible := isCompatible_map_equiv e N N eN (fun _ => rfl) eQ (fun _ => rfl)
        D.groupHaar D.unipotentHaar D.measure D.compatible }

/-- The homeomorphism `N g ↦ N t g z`, for the change-of-character diagonal `t` and any
right translation by `z`. -/
def shiftQuotient (a : ℂˣ) (z : G) : Q ≃ₜ Q :=
  (changeConjugationQuotient a).trans (rightTranslate N (changeDiagonal r a * z))

theorem shiftQuotient_mk (a : ℂˣ) (z g : G) :
    shiftQuotient a z (Quotient.mk _ g) = Quotient.mk _ (changeDiagonal r a * g * z) := by
  change Quotient.mk _ (changeDiagonal r a * g * (changeDiagonal r a)⁻¹ *
    (changeDiagonal r a * z)) = _
  congr 1
  group

/-- Both conjugation and the subsequent right translation use the same transported
compatible quotient measure. -/
theorem measurePreserving_shiftQuotient (a : ℂˣ) (D : ComplexQuotientMeasureData r) (z : G) :
    MeasurePreserving (shiftQuotient a z) D.measure (changeQuotientMeasure a D).measure := by
  have h : MeasurePreserving (changeConjugationQuotient a) D.measure
      (changeQuotientMeasure a D).measure :=
    ⟨(changeConjugationQuotient a).continuous.measurable, rfl⟩
  let := (changeQuotientMeasure a D).unipotentHaar_rightInvariant
  exact ((changeQuotientMeasure a D).compatible.right_invariant _).comp h

private theorem complexScaledCharacter_neg_parameter (a : ℂˣ) (x : ℂ) :
    (complexScaledCharacter (-a)).complex x = (complexScaledCharacter a).complex (-x) := by
  change ((complexScaledCharacter (-a) x : Circle) : ℂ) =
    ((complexScaledCharacter a (-x) : Circle) : ℂ)
  rw [complexScaledCharacter_apply, complexScaledCharacter_apply, Units.val_neg, neg_mul,
    mul_neg]

theorem whittakerCharacter_neg_parameter (a : ℂˣ) (u : G) :
    complexWhittakerCharacter a u * complexWhittakerCharacter (-a) u = 1 := by
  unfold complexWhittakerCharacter
  rw [complexScaledCharacter_neg_parameter, ← AddChar.map_add_eq_mul, add_neg_cancel,
    AddChar.map_zero_eq_one]

private theorem isUnitriangular_of_mem (u : N) :
    PrimitiveAdelicHeight.IsUnitriangular u.val.val :=
  ⟨u.property.1, u.property.2⟩

private theorem dualFunction_unipotent_mul {ds : List ComplexCharacterData} {a : ℂˣ}
    {W : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a) (u : N) (g : G) :
    ArchimedeanLocal.dualFunction (r + 1) W (u.val * g) =
      complexWhittakerCharacter (-a) u.val * ArchimedeanLocal.dualFunction (r + 1) W g := by
  let v : N := ⟨Unfolding.dualConjGL (r + 1) ℂ u.val,
    Unfolding.isUnitriangular_dualConjGL _ _ _ (isUnitriangular_of_mem u⁻¹)⟩
  have hv :
      GeneralLinear.weylLong (r + 1) ℂ * GeneralLinear.inverseTranspose (r + 1) ℂ (u.val * g) =
        v.val * (GeneralLinear.weylLong (r + 1) ℂ *
          GeneralLinear.inverseTranspose (r + 1) ℂ g) := by
    dsimp [v]
    rw [Unfolding.dualConjGL_apply, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (GeneralLinear.weylLong (r + 1) ℂ) (GeneralLinear.weylLong (r + 1) ℂ),
      GeneralLinear.weylLong_mul_self, one_mul]
  have hχ : complexWhittakerCharacter a v.val = complexWhittakerCharacter (-a) u.val := by
    change (complexScaledCharacter a).complex
      (∑ i : Fin r, (Unfolding.dualConjGL (r + 1) ℂ u.val).val i.castSucc i.succ) =
        (complexScaledCharacter (-a)).complex _
    rw [complexScaledCharacter_neg_parameter,
      Unfolding.sum_superdiag_dualConjGL ℂ _ (isUnitriangular_of_mem u)
        (isUnitriangular_of_mem u⁻¹)]
  unfold ArchimedeanLocal.dualFunction
  rw [hv, model_unipotent_mul hW, hχ]

theorem model_pair_invariant {ds ds' : List ComplexCharacterData} {a : ℂˣ}
    {W W' : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hW' : W' ∈ complexWhittakerModel r ds' (-a)) (u : N) (g : G) :
    W (u.val * g) * W' (u.val * g) = W g * W' g := by
  rw [model_unipotent_mul hW, model_unipotent_mul hW', mul_mul_mul_comm,
    whittakerCharacter_neg_parameter, one_mul]

theorem dual_pair_invariant {ds ds' : List ComplexCharacterData} {a : ℂˣ}
    {W W' : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hW' : W' ∈ complexWhittakerModel r ds' (-a)) (u : N) (g : G) :
    ArchimedeanLocal.dualFunction (r + 1) W (u.val * g) *
        ArchimedeanLocal.dualFunction (r + 1) W' (u.val * g) =
      ArchimedeanLocal.dualFunction (r + 1) W g * ArchimedeanLocal.dualFunction (r + 1) W' g := by
  rw [dualFunction_unipotent_mul hW, dualFunction_unipotent_mul hW',
    mul_mul_mul_comm, whittakerCharacter_neg_parameter, one_mul]

/-- Evaluate the quotient integrand at any representative, using the left invariance
of the product of the two coefficient functions. -/
theorem complexEqualIntegrand_mk {W W' : G → ℂ}
    (h : ∀ (u : N) g, W (u.val * g) * W' (u.val * g) = W g * W' g)
    (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) (g : G) :
    complexEqualIntegrand W W' Φ s (Quotient.mk _ g) =
      W g * W' g * Φ (Langlands.RankinSelberg.lastRow g) *
        ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  let F := fun x => W x * W' x * Φ (Langlands.RankinSelberg.lastRow x) *
    ArchimedeanLocal.detPower complexNormalizedAbs x s
  have hF (u : N) (x : G) : F (u.val * x) = F x := by
    simp only [F, h, lastRow_unipotent_mul, ArchimedeanLocal.detPower, Units.val_mul,
      Matrix.det_mul, unipotent_det, one_mul]
  exact congrArg (descend N F hF) (Quotient.out_eq (Quotient.mk _ g))

end Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange
