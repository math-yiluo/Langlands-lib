import Langlands.Representation.Archimedean.RealCartanLowerCoordinates

/-! # Block splitting of the projected Cartan Jacobian -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanArgumentJacobian

open RealCartanLowerCoordinates RealCartanPeakTest RealCartanArgumentDifferential
  RealLeviCartanDifferential RealLeviChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "N" => ∑ i, sz i
local notation "Mat" => Matrix (Fin N) (Fin N) ℝ
local notation "K" => Matrix.unitaryGroup (Fin N) ℝ
local notation "XSpace" => (Coord sz → ℝ)
local notation "ZSpace" => (WithinIndex sz → ℝ)
local notation "Lower" => (LowerIndex N → ℝ)

/-- Fill the skew matrix of the within-block lower coordinate variations. -/
def interiorSkew : ZSpace →L[ℝ] Mat :=
  (skewLower N).comp ((joinLower sz : (XSpace × ZSpace) →L[ℝ] Lower).comp
    (ContinuousLinearMap.inr ℝ XSpace ZSpace))

@[simp]
theorem interiorSkew_apply (z : ZSpace) :
    interiorSkew sz z = skewLower N (joinLower sz (0, z)) := rfl

theorem interiorSkew_transpose (z : ZSpace) : (interiorSkew sz z)ᵀ = -(interiorSkew sz z) :=
  transpose_skewLower _

theorem lowerProjection_transverseSkew (X : XSpace) :
    lowerProjection N (transverseSkew sz X) = joinLower sz (X, 0) := by
  funext p
  obtain ⟨a, rfl⟩ := (lowerIndexEquiv sz).surjective p
  cases a with
  | inl p =>
    rw [joinLower_apply_off, lowerProjection_apply, lowerIndexEquiv_inl,
      transverseSkew_apply_of_lt sz X (lt_of_cls_lt sz p.2), strict_apply_coord]
  | inr p =>
    rw [joinLower_apply_within, lowerProjection_apply, lowerIndexEquiv_inr,
      transverseSkew_apply_of_lt sz X p.1.2, strict_apply_of_not_lt X p.2]
    rfl

private theorem val_mul_transpose (B : K) : (B : Mat) * (B : Mat)ᵀ = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.mem_unitaryGroup_iff.mp B.2

private theorem strict_adLin (B : K) (hB : BlockZero sz (B : Mat)) (X : XSpace) :
    strict (adLin (B : Mat) X) = (B : Mat) * strict X * (B : Mat)ᵀ := by
  ext p q
  by_cases hpq : cls sz q < cls sz p
  · exact strict_apply_coord (adLin (B : Mat) X) ⟨(p, q), hpq⟩
  · have hk := val_mul_transpose sz B
    have hz := lower_conj_apply_of_not_lt hk hB X hpq
    rw [lower_eq_strict_add_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hk,
      Matrix.add_apply] at hz
    rw [strict_apply_of_not_lt _ hpq]
    linarith

theorem conjugation_transverseSkew (B : K) (hB : BlockZero sz (B : Mat)) (X : XSpace) :
    conjugationCLM (B : Mat) (transverseSkew sz X) = transverseSkew sz (adLin (B : Mat) X) := by
  rw [conjugationCLM_apply, transverseSkew_apply, transverseSkew_apply, strict_adLin sz B hB,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- The transverse difference in the off-block coordinates. -/
def transverseDifference (d : Fin N → ℝ) (B : K) : XSpace →L[ℝ] XSpace :=
  ContinuousLinearMap.id ℝ XSpace - ((adLin (B : Mat) (sz := sz)).toContinuousLinearMap).comp
    (radialScale sz d)

theorem transverseDifference_apply (d : Fin N → ℝ) (B : K) (X : XSpace) :
    transverseDifference sz d B X = X - adLin (B : Mat) (radialScale sz d X) := rfl

theorem argumentDerivative_block_split (d : Fin N → ℝ) (B W : K)
    (hB : BlockZero sz (B : Mat)) :
    argumentDerivative sz d (B : Mat) (W : Mat) (interiorSkew sz) =
      (projectedConjugation W⁻¹).comp ((joinLower sz : (XSpace × ZSpace) →L[ℝ] Lower).comp
        ((transverseDifference sz d B).prodMap (-ContinuousLinearMap.id ℝ ZSpace))) := by
  apply ContinuousLinearMap.ext
  rintro ⟨X, Z⟩
  have hW : ((W⁻¹ : K) : Mat) = (W : Mat)ᵀ := by
    change star (W : Mat) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  let H := transverseSkew sz X - conjugationCLM (B : Mat) (transverseSkew sz (radialScale sz d X)) -
    interiorSkew sz Z
  change lowerProjection N (conjugationCLM (W : Mat)ᵀ H) = projectedConjugation W⁻¹
    (joinLower sz (transverseDifference sz d B X, -Z))
  have hH : Hᵀ = -H := by
    simp only [H, Matrix.transpose_sub, transverseSkew_transpose,
      conjugation_transpose_eq_neg _ _ (transverseSkew_transpose _ _), interiorSkew_transpose]
    abel
  have hL : lowerProjection N H = joinLower sz (transverseDifference sz d B X, -Z) := by
    simp only [H, map_sub, conjugation_transverseSkew sz B hB,
      lowerProjection_transverseSkew, interiorSkew_apply, lowerProjection_skewLower]
    rw [← map_sub, ← map_sub]
    simp only [Prod.mk_sub_mk, sub_zero, sub_self, zero_sub, transverseDifference_apply]
  rw [projectedConjugation_apply, hW, ← hL, skewLower_lowerProjection hH]

/-- The determinant after identifying the domain with the full lower entries. -/
def argumentLowerEnd (d : Fin N → ℝ) (B W : K) : Lower →L[ℝ] Lower :=
  (argumentDerivative sz d (B : Mat) (W : Mat) (interiorSkew sz)).comp
    (joinLower sz).symm.toContinuousLinearMap

theorem abs_det_argumentLowerEnd (d : Fin N → ℝ) (B W : K)
    (hB : BlockZero sz (B : Mat)) :
    |(argumentLowerEnd sz d B W).det| = |(transverseDifference sz d B).det| := by
  rw [argumentLowerEnd, argumentDerivative_block_split sz d B W hB]
  let A := (transverseDifference sz d B).toLinearMap
  let I := (LinearMap.id : ZSpace →ₗ[ℝ] ZSpace)
  let E := (joinLower sz).toLinearEquiv
  change |LinearMap.det ((projectedConjugation W⁻¹).toLinearMap.comp
    (E.toLinearMap.comp ((A.prodMap (-I)).comp E.symm.toLinearMap)))| = |A.det|
  rw [LinearMap.det_comp, abs_mul, abs_det_projectedConjugation, one_mul,
    LinearMap.det_conj, LinearMap.det_prodMap, abs_mul, ← neg_one_smul ℝ I,
    LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow, abs_neg, abs_one, one_pow, mul_one]

/-- The within-block angles and the orthogonal frame do not change the
absolute determinant of the Cartan derivative in flat lower coordinates. -/
def RealCartanArgumentJacobianStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ) (d : Fin (∑ i, sz i) → ℝ)
    (B W : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ),
    BlockZero sz (B : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) →
    |(argumentLowerEnd sz d B W).det| = |(transverseDifference sz d B).det|

theorem realCartanArgumentJacobian : RealCartanArgumentJacobianStatement :=
  fun _ _ _ _ _ hB => abs_det_argumentLowerEnd _ _ _ _ hB

end Langlands.Archimedean.RealCartanArgumentJacobian
