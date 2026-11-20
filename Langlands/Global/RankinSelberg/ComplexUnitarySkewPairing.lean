import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Skew symmetry of the compact Lie derivatives in the unitary integral -/

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean

variable {n : ℕ}
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "R" => rightDerivative (matrixModel ℂ n)

private theorem matrix_star_unitary (k : K) : star k.val.val = (k⁻¹ : K).val.val :=
  Units.eq_inv_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff'.1 k.property)

variable [MeasurableSpace (unitaryCompact ℂ n)] [BorelSpace (unitaryCompact ℂ n)]

/-- The Hermitian pairing given by restriction to the unitary compact group. -/
def complexUnitaryPairing (μ : Measure K) (f g : G → ℂ) : ℂ :=
  ∫ k : K, star (f k.val) * g k.val ∂μ

/-- Right differentiation in a skew-Hermitian direction is skew symmetric
for the unitary integral. -/
theorem complexUnitaryPairing_rightDerivative_add_eq_zero (μ : Measure K)
    [μ.IsHaarMeasure] [μ.IsInvInvariant] {X : M} (hX : X.conjTranspose = -X)
    {f g : G → ℂ} (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ g)
    (hRf : Continuous (R X f)) (hRg : Continuous (R X g)) :
    complexUnitaryPairing μ (R X f) g + complexUnitaryPairing μ f (R X g) = 0 := by
  let U : Set M := {y | IsUnit y}
  let F : M → ℂ := fun y => star (unitsExtension f y) * unitsExtension g y
  let A : M →L[ℝ] M := (starL' ℝ : M ≃L[ℝ] M).toContinuousLinearMap
  have hFs : ContDiffOn ℝ ∞ F U :=
    ((Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_unitsExtension hf))).mul
      (contDiffOn_unitsExtension hg)
  have hAU : Set.MapsTo A U U := fun y h => by
    show IsUnit (star y)
    exact h.star
  have hFa : ContDiffOn ℝ 1 (F ∘ A) U :=
    ((hFs.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp A.contDiff.contDiffOn hAU)
  have h0 := ComplexDuality.LieInvariance.integral_fderiv_mul_eq_zero μ hFa hX
  let H (k : K) := star (R X f k.val) * g k.val + star (f k.val) * R X g k.val
  have hDeriv (k : K) : fderiv ℝ (F ∘ A) k.val.val (X * k.val.val) = -H k⁻¹ := by
    let ku := k⁻¹
    have hAk : A k.val.val = ku.val.val := matrix_star_unitary k
    have hAX : A (X * k.val.val) = -(ku.val.val * X) := by
      change star (X * k.val.val) = _
      rw [star_mul, matrix_star_unitary, Matrix.star_eq_conjTranspose, hX, mul_neg]
    have hFd : DifferentiableAt ℝ F (A k.val.val) :=
      ((hFs (A k.val.val) (hAU k.val.isUnit)).contDiffAt
        (isOpen_setOf_isUnit_matrix.mem_nhds (hAU k.val.isUnit))).differentiableAt (by simp)
    rw [(hFd.hasFDerivAt.comp _ A.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,
      hAk, hAX, map_neg, neg_inj]
    have hd₁ := (differentiableAt_unitsExtension hf ku.val.isUnit).hasFDerivAt.star
    have hd₂ := (differentiableAt_unitsExtension hg ku.val.isUnit).hasFDerivAt
    change fderiv ℝ ((fun y => star (unitsExtension f y)) * unitsExtension g)
      ku.val.val (ku.val.val * X) = H k⁻¹
    rw [(hd₁.mul hd₂).fderiv]
    simp only [H, add_apply, unitsExtension_val,
      rightDerivative_eq_fderiv hf, rightDerivative_eq_fderiv hg]
    let p := (fderiv ℝ (unitsExtension f) ku.val.val) (ku.val.val * X)
    let q := (fderiv ℝ (unitsExtension g) ku.val.val) (ku.val.val * X)
    change star (f ku.val) * q + g ku.val * star p =
      star p * g ku.val + star (f ku.val) * q
    ring
  change (∫ k : K, fderiv ℝ (F ∘ A) k.val.val (X * k.val.val) ∂μ) = 0 at h0
  simp_rw [hDeriv] at h0
  rw [integral_neg, integral_inv_eq_self, neg_eq_zero] at h0
  change _ + _ = _
  unfold complexUnitaryPairing
  rw [← integral_add]
  · exact h0
  all_goals
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  · exact ((hRf.comp continuous_subtype_val).star).mul
      (hg.continuous.comp continuous_subtype_val)
  · exact ((hf.continuous.comp continuous_subtype_val).star).mul
      (hRg.comp continuous_subtype_val)

end Langlands.Global.RankinSelbergGlobal
