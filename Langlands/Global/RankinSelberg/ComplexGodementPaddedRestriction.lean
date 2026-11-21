import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices

/-! # Restriction of the complex Godement integral to the padded group -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementPaddedRestriction

open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rectangularJoin partialFourierPlusIntegral
  rectangularJoin_castSucc rectangularJoin_last rectangularJoin_split partialFourierPlusIntegral_join)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodement (normPower characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply complexGodementIteratedIntegral)
open ComplexGodementWhittaker (augmentedPoint augmentedPoint_castSucc augmentedPoint_last kernelBase)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 2) ℂ
local notation "Sq" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ
local notation "pad₁[" m "]" => padGL (R := ℂ) (Nat.le_succ (m + 1))
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

private theorem equiv_det_pad₁ (g : G) : determinant (pad₁[r] g) = determinant g :=
  Units.ext (UnequalAnalytic.det_padGL _ g)

private theorem detPower_pad₁ (g : G) (s : ℂ) : P (pad₁[r] g) s = P g s := by
  unfold ArchimedeanLocal.detPower
  rw [UnequalAnalytic.det_padGL]

/-- Right multiplication by a padded group element acts on the square part of the test. -/
theorem rectangularJoin_mul_pad (A : Sq) (v : Vec) (g : G) :
    rectangularJoin A v * (pad₁[r] g).val = rectangularJoin (A * g.val) v := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    have h := UnequalAnalytic.padGL_col (Nat.le_succ (r + 1)) g (Fin.last (r + 1)) (by simp)
    simp only [Matrix.mul_apply, h, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, rectangularJoin_last]
  | cast j =>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, rectangularJoin_castSucc, Matrix.mul_apply]
    have hlast : (pad₁[r] g).val (Fin.last (r + 1)) j.castSucc = 0 := by
      rw [UnequalAnalytic.padGL_row _ g _ (by simp), Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm]
    have hcast (k : Fin (r + 1)) : (pad₁[r] g).val k.castSucc j.castSucc = g.val k j := by
      rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨k.isLt, j.isLt⟩]
      rfl
    simp only [hlast, hcast, rectangularJoin_castSucc, mul_zero, add_zero]

private theorem partialSchwartz_rightTest_pad (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ)
    (Φ : 𝓢(Rect, ℂ)) (A : Sq) (v : Vec) (g : G) :
    partialSchwartz a μ (rightTest (pad₁[r] g) Φ) (rectangularJoin A v) =
      partialSchwartz a μ Φ (rectangularJoin (A * g.val) v) := by
  simp only [partialSchwartz_apply, partialFourierPlusIntegral_join,
    rightTest_apply, rectangularJoin_mul_pad]

/-- The normalized complex power agrees with its additive logarithm presentation. -/
theorem normPower_determinant {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (s : ℂ) :
    normPower s (determinant g) = P g s := by
  change ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s = _
  have hp : 0 < complexNormalizedAbs g.val.det := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
  simp only [ArchimedeanLocal.detPower, mul_comm _ s]

/-- The group integrand after changing the Godement variable by a right translation.
The last row of `g * h⁻¹` is the inverse-transpose frequency after this change. -/
def paddedRestrictionKernel (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (W : G → ℂ) (g b : G) (s : ℂ) (h : G) : ℂ :=
  partialSchwartz a μ Φ (rectangularJoin (h.val * b.val) ((g * h⁻¹).val (Fin.last r))) *
    W (g * h⁻¹) * characterWeight d (((r + 2 : ℕ) : ℂ) / 2 + s - 1) (determinant h)

private theorem paddedRestrictionKernel_change (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (W : G → ℂ) (g b : G) (s : ℂ) (h : G) :
    iteratedKernel (complexScaledCharacter a) μ d (rightTest (pad₁[r] (g * b)) Φ) W
      (((r + 2 : ℕ) : ℂ) / 2 + s) (h * g⁻¹) *
        characterWeight d (((r + 2 : ℕ) : ℂ) / 2 + s - 1) (determinant g) =
      paddedRestrictionKernel μ d a Φ W g b s h := by
  let Ψ := rightTest (pad₁[r] (g * b)) Φ
  let e : ℂ := ((r + 2 : ℕ) : ℂ) / 2 + s - 1
  rw [iteratedKernel_eq (complexScaledCharacter a) μ d Ψ (partialSchwartz a μ Ψ)
    (partialSchwartz_apply a μ Ψ)]
  rw [kernelBase]
  have hPt (x : G) :
      augmentedPoint x = rectangularJoin x.val (x⁻¹.val (Fin.last r)) := by
    ext i j
    induction j using Fin.lastCases <;> simp
  rw [hPt, partialSchwartz_rightTest_pad]
  have hgb : (h * g⁻¹).val * (g * b).val = h.val * b.val := by
    rw [← Units.val_mul, ← Units.val_mul, mul_assoc, inv_mul_cancel_left]
  rw [hgb, mul_inv_rev, inv_inv]
  have he (x : G) : (d.character (determinant x) : ℂ) * P x e =
      characterWeight d e (determinant x) := by
    rw [← normPower_determinant]
    rfl
  unfold paddedRestrictionKernel
  let z := partialSchwartz a μ Φ (rectangularJoin (h.val * b.val) ((g * h⁻¹).val (Fin.last r))) * W (g * h⁻¹)
  change z * (d.character (determinant (h * g⁻¹)) : ℂ) * P (h * g⁻¹) e *
    characterWeight d e (determinant g) = z * characterWeight d e (determinant h)
  rw [mul_assoc z, he, mul_assoc z, ← map_mul, ← map_mul, inv_mul_cancel_right]

/-- For a fixed padded argument, the changed Godement integral is absolutely convergent.
The factor on the translated smaller group variable is the half power of its determinant. -/
def ComplexGodementPaddedRestrictionStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (ν : Measure (Langlands.GeneralLinear (r + 1) ℂ)),
    ν.IsHaarMeasure → ν.IsMulRightInvariant →
  ∀ (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ, ℂ))
    (W : complexWhittakerModel r ds (-a)) (g b : Langlands.GeneralLinear (r + 1) ℂ) (s : ℂ),
    Integrable (paddedRestrictionKernel μ d a Φ W.val g b s) ν ∧
    continuedValue ν μ d a Φ W.val (padGL (Nat.le_succ (r + 1)) (g * b)) s =
      (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * P g (1 / 2) *
        characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant b) *
        ∫ h, paddedRestrictionKernel μ d a Φ W.val g b s h ∂ν

theorem complexGodementPaddedRestriction : ComplexGodementPaddedRestrictionStatement := by
  intro r ds a ν hν hνR μ d Φ W g b s
  let : ν.IsMulRightInvariant := hνR
  let Ψ := rightTest (pad₁[r] (g * b)) Φ
  let t : ℂ := ((r + 2 : ℕ) : ℂ) / 2 + s
  let c := characterWeight d (t - 1) (determinant g)
  let f := iteratedKernel (complexScaledCharacter a) μ d Ψ W.val t
  have hf : Integrable f ν := by
    have h := (complexGodementIteratedIntegral r ds (-a) ν hν μ d Ψ W).1 t
    rwa [neg_neg] at h
  have hChange : (fun h => f (h * g⁻¹) * c) = paddedRestrictionKernel μ d a Φ W.val g b s :=
    funext (paddedRestrictionKernel_change μ d a Φ W.val g b s)
  refine ⟨?_, ?_⟩
  · rw [← hChange]
    have h := (measurePreserving_mul_right ν g⁻¹).integrable_comp_of_integrable hf
    exact h.mul_const c
  have hv : (∫ h, paddedRestrictionKernel μ d a Φ W.val g b s h ∂ν) =
      (∫ h, f h ∂ν) * c := by
    rw [← hChange, integral_mul_const, integral_mul_right_eq_self]
  have hs : characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant (pad₁[r] (g * b))) *
      P (pad₁[r] (g * b)) s =
      P g (1 / 2) * characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant b) * c := by
    have ht : ((r + 1 : ℕ) : ℂ) / 2 + s = t - 1 + 1 / 2 := by
      unfold t
      push_cast
      ring
    have hP {x : Langlands.GeneralLinear (r + 1) ℂ} (u v : ℂ) :
        P x (u + v) = P x u * P x v := by
      unfold ArchimedeanLocal.detPower
      rw [add_mul, Complex.exp_add]
    rw [equiv_det_pad₁, detPower_pad₁, ← normPower_determinant]
    have hχ : characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant (g * b)) *
        normPower s (determinant (g * b)) =
        characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant (g * b)) := by
      change ((d.character _ : ℂ) * normPower _ _) * normPower _ _ =
        (d.character _ : ℂ) * normPower _ _
      simp only [normPower_determinant, hP]
      rw [mul_assoc]
    have hcg : characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant g) = c * P g (1 / 2) := by
      rw [ht]
      change (d.character _ : ℂ) * normPower _ _ =
        ((d.character _ : ℂ) * normPower _ _) * _
      rw [normPower_determinant, normPower_determinant, hP, mul_assoc]
    rw [hχ, map_mul, map_mul, hcg]
    ring
  rw [hv, continuedValue]
  rw [show (((r + 1 : ℕ) : ℂ) + 1) / 2 + s = t by dsimp [t]; push_cast; ring]
  change (_ * characterWeight d _ _) * P (pad₁[r] (g * b)) s * (∫ h, f h ∂ν) = _
  rw [mul_assoc (_ : ℂ) (characterWeight d _ _) (P (pad₁[r] (g * b)) s), hs]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGodementPaddedRestriction
