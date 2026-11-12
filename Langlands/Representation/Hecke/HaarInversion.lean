import Langlands.Representation.Hecke.Convolution
import Langlands.Analysis.Local.ModularCharacterRegularityProof
import Mathlib.Algebra.Ring.Opposite

/-! # Haar-weighted inversion on the existing Hecke algebra

The function model of inversion of Haar distributions, used in Renard III.2.1.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure MulOpposite
open scoped NNReal

namespace Langlands.Hecke

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G]

/-- Mathlib's right-pushforward Haar factor, viewed as a complex character.
It is the inverse of Renard's modular function `δ`. -/
def haarScale : G →* ℂ where
  toFun g := ((modularCharacter g : ℝ) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

@[simp] theorem haarScale_mul_inverse (g : G) :
    haarScale g * haarScale g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem haarScale_locallyConstant : IsLocallyConstant (haarScale (G := G)) :=
  Haar.isLocallyConstant_modularCharacter.comp (fun r : ℝ≥0 => ((r : ℝ) : ℂ))

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-- Inversion of a Haar distribution, on the original test-function carrier.
The modular factor is essential for the distribution interpretation. -/
def haarInversion : HeckeAlgebra μ ≃ₗ[ℂ] HeckeAlgebra μ where
  toFun f :=
    ⟨fun x => haarScale x * f x⁻¹,
      haarScale_locallyConstant.mul (f.locallyConstant.comp_continuous continuous_inv),
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mul_left⟩
  invFun f :=
    ⟨fun x => haarScale x * f x⁻¹,
      haarScale_locallyConstant.mul (f.locallyConstant.comp_continuous continuous_inv),
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mul_left⟩
  left_inv f := by
    apply HeckeAlgebra.ext
    intro x
    change haarScale x * (haarScale x⁻¹ * f (x⁻¹)⁻¹) = f x
    rw [← mul_assoc, haarScale_mul_inverse, one_mul, inv_inv]
  right_inv f := by
    apply HeckeAlgebra.ext
    intro x
    change haarScale x * (haarScale x⁻¹ * f (x⁻¹)⁻¹) = f x
    rw [← mul_assoc, haarScale_mul_inverse, one_mul, inv_inv]
  map_add' f g := by
    apply HeckeAlgebra.ext
    intro x
    exact mul_add _ _ _
  map_smul' c f := by
    apply HeckeAlgebra.ext
    intro x
    exact mul_left_comm _ c _

@[simp] theorem haarInversion_apply (f : HeckeAlgebra μ) (x : G) :
    haarInversion μ f x = haarScale x * f x⁻¹ := rfl

@[simp] theorem haarInversion_involution (f : HeckeAlgebra μ) :
    haarInversion μ (haarInversion μ f) = f :=
  (haarInversion μ).left_inv f

variable [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

/-- Haar inversion reverses convolution, without unimodularity. -/
theorem haarInversion_mul (f g : HeckeAlgebra μ) :
    haarInversion μ (f * g) = haarInversion μ g * haarInversion μ f := by
  apply HeckeAlgebra.ext
  intro x
  change haarScale x * (∫ y, f y * g (y⁻¹ * x⁻¹) ∂μ) =
    ∫ y, (haarScale y * g y⁻¹) *
      (haarScale (y⁻¹ * x) * f (y⁻¹ * x)⁻¹) ∂μ
  rw [← integral_const_mul]
  rw [← integral_mul_left_eq_self
    (fun y => (haarScale y * g y⁻¹) *
      (haarScale (y⁻¹ * x) * f (y⁻¹ * x)⁻¹)) x]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [mul_inv_rev, inv_mul_cancel_right, inv_inv, map_mul]
  have hy := haarScale_mul_inverse y
  calc
    _ = haarScale x * (f y * g (y⁻¹ * x⁻¹)) := rfl
    _ = (haarScale x * (haarScale y * haarScale y⁻¹)) *
        (f y * g (y⁻¹ * x⁻¹)) := by rw [hy, mul_one]
    _ = _ := by ring

end Langlands.Hecke
