import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Global.RankinSelberg.ComplexLocalUnitaryMatrixFourier
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # Transport of a reproducing compact weight to the dual square test -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open scoped Langlands.Archimedean.ComplexDuality

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

variable {n : ℕ}

local notation "Kc" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "ι" => GeneralLinear.inverseTranspose n ℂ
local notation "F[" a "]" => rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
local notation "μ[" a "]" => RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) n n

local instance fourierMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance fourierOppositeSecondCountable : SecondCountableTopology Matᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology
local instance fourierGroupSecondCountable : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isInducing_embedProduct.secondCountableTopology

/-- Inverse transpose restricted to the compact unitary group. -/
def complexUnitaryInverseTranspose (n : ℕ) : unitaryCompact ℂ n →* unitaryCompact ℂ n where
  toFun k := ⟨GeneralLinear.inverseTranspose n ℂ k.val,
    Matrix.transpose_mem_unitaryGroup_iff.mpr (k⁻¹).2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' k l := Subtype.ext (map_mul _ k.val l.val)

theorem continuous_complexUnitaryInverseTranspose :
    Continuous (complexUnitaryInverseTranspose n) :=
  ((GeneralLinear.continuous_inverseTranspose n ℂ).comp continuous_subtype_val).subtype_mk _

private def matrixShear : Kc × Mat ≃ᵐ Kc × Mat where
  toFun p := (p.1, (p.1.val⁻¹).val * p.2)
  invFun p := (p.1, p.1.val.val * p.2)
  left_inv := by
    rintro ⟨k, Y⟩
    simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  right_inv := by
    rintro ⟨k, Y⟩
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  measurable_toFun := (continuous_fst.prodMk
    (((Units.continuous_val.comp continuous_subtype_val.inv).comp continuous_fst).matrix_mul
      continuous_snd)).measurable
  measurable_invFun := (continuous_fst.prodMk
    (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mul
      continuous_snd)).measurable

variable (n) in
/-- A compact weight reproducing an integrable square test also reproduces
its Fourier transform with the opposite determinant twist and with the
compact translates parametrized by inverse transpose. -/
def ComplexLocalCompactFourierWeightStatement : Prop :=
  ∀ (a : ℂˣ) (ν : Measure Kc), ν.IsHaarMeasure →
  ∀ (κ : Kc → ℂ), Continuous κ →
  ∀ (η : ℂˣ →* ℂˣ), Continuous η →
  ∀ (Φ : Mat → ℂ), Integrable Φ μ[a] →
    (∀ X, ∫ k, κ k * complexCompactMatrixTranslate (η.comp invMonoidHom) Φ k X ∂ν = Φ X) →
  ∀ X, (∫ k, κ k * complexCompactMatrixTranslate η (F[a] Φ)
    (complexUnitaryInverseTranspose n k) X ∂ν) = F[a] Φ X

theorem complexLocalCompactFourierWeight : ComplexLocalCompactFourierWeightStatement n := by
  intro a ν hν κ hκ η hη Φ hΦ hRepro X
  let : ν.IsHaarMeasure := hν
  let μM := μ[a]
  let ψ := complexScaledCharacter a
  let νC := complexSelfDualMeasure a
  let : νC.measure.IsAddHaarMeasure := νC.isAddHaar
  let : μM.IsAddHaarMeasure := RankinSelberg.rectangularMeasure_isAddHaar νC n n
  let c (k : Kc) : ℂ := κ k * (η (GeneralLinear.determinant k.val)⁻¹ : ℂ)
  have hc : Continuous c := hκ.mul (Units.continuous_val.comp
    (hη.comp ((GeneralLinear.determinantContinuous.continuous.comp continuous_subtype_val).inv)))
  have hcInt : Integrable c ν := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace c)
  let H (p : Kc × Mat) : ℂ := c p.1 * Φ ((p.1.val⁻¹).val * p.2)
  let e := matrixShear (n := n)
  have he : MeasurePreserving e (ν.prod μM) (ν.prod μM) :=
    (MeasurePreserving.id ν).skew_product
      (((Units.continuous_val.comp continuous_subtype_val.inv).comp continuous_fst).matrix_mul
        continuous_snd).measurable
      (Filter.Eventually.of_forall fun k =>
        (measurePreserving_complexUnitaryMatrixLeft μM k⁻¹).map_eq)
  have hH : Integrable H (ν.prod μM) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr (hcInt.mul_prod hΦ)
  let B (p : Kc × Mat) := H p * ψ.complex (rectangularPairing p.2 X)
  have hB : Integrable B (ν.prod μM) := by
    refine hH.mono (hH.aestronglyMeasurable.mul ?_) (Filter.Eventually.of_forall fun p => ?_)
    · exact (ψ.continuous_complex.comp ((continuous_rectangularPairing_left X).comp
        continuous_snd)).aestronglyMeasurable
    · simp only [B, norm_mul, ψ.norm_complex, mul_one, le_refl]
  symm
  calc
    (F[a] Φ X) = ∫ Y : Mat, ∫ k : Kc, B (k, Y) ∂ν ∂μM := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun Y => ?_
      change Φ Y * ψ.complex (rectangularPairing Y X) = ∫ k, B (k, Y) ∂ν
      have hY : (∫ k, H (k, Y) ∂ν) = Φ Y := by
        simpa only [H, c, complexCompactMatrixTranslate, mul_assoc, MonoidHom.comp_apply,
          invMonoidHom_apply] using hRepro Y
      rw [← hY, ← integral_mul_const]
    _ = ∫ p, B p ∂ν.prod μM := (integral_prod_symm _ hB).symm
    _ = ∫ k : Kc, ∫ Y : Mat, B (k, Y) ∂μM ∂ν := integral_prod _ hB
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun k => ?_
      have hdet : GeneralLinear.determinant (ι k.val) = (GeneralLinear.determinant k.val)⁻¹ :=
        Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose _
      calc
        (∫ Y, B (k, Y) ∂μM) = c k * F[a] (fun Y => Φ ((k.val⁻¹).val * Y)) X := by
          simp only [B, H, mul_assoc, integral_const_mul]
          rfl
        _ = c k * F[a] Φ ((ι k.val⁻¹).val * X) :=
          congrArg (fun z : ℂ => c k * z) (complexLocalUnitaryMatrixFourier a k⁻¹ Φ X)
        _ = κ k * complexCompactMatrixTranslate η (F[a] Φ) (complexUnitaryInverseTranspose n k) X := by
          simp only [c, complexCompactMatrixTranslate, complexUnitaryInverseTranspose, MonoidHom.coe_mk,
            OneHom.coe_mk, hdet, map_inv, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
