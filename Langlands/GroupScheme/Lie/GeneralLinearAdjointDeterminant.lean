import Langlands.GroupScheme.Lie.GeneralLinearAdjoint
import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Langlands.GroupScheme.Rational.GeneralLinearCharacterClassification
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-! # The adjoint determinant of the actual general linear group -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n]
  (k : Type u) [Field k] [CharZero k]

local instance : IsAffine (groupScheme n (CommRingCat.of k)).X.left := isAffine_groupScheme n _
local instance : Smooth (groupScheme n (CommRingCat.of k)).X.hom := smoothStatement n _

omit [CharZero k] in
/-- Scalar matrices act trivially on the actual dual-number Lie kernel. -/
theorem adjoint_scalar_eq_id (z : kˣ) :
    adjoint (groupScheme n (CommRingCat.of k)) k
      ((affinePointsEquiv n (CommRingCat.of k) (CommAlgCat.of k k)).symm
        (Matrix.GeneralLinearGroup.scalar n z)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := (DualNumber.pointKernelLinearEquiv
    (n := n) (R := CommRingCat.of k) (A := k)).surjective x
  rw [DualNumber.adjoint_pointKernelLinearEquiv, MulEquiv.apply_symm_apply]
  change DualNumber.pointKernelLinearEquiv
    ((Matrix.GeneralLinearGroup.scalar n z : Matrix n n k) * X *
      (((Matrix.GeneralLinearGroup.scalar n z)⁻¹ : GL n k) : Matrix n n k)) =
      DualNumber.pointKernelLinearEquiv X
  congr 1
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_comm _ (Commute.all _)]
  change X * (Matrix.GeneralLinearGroup.scalar n z : Matrix n n k) *
    (((Matrix.GeneralLinearGroup.scalar n z)⁻¹ : GL n k) : Matrix n n k) = X
  rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

/-- The determinant character of conjugation is zero for the actual GL group. -/
theorem adjointDeterminantCharacter_eq_zero :
    Lie.adjointDeterminantCharacter (groupScheme n (CommRingCat.of k)) = 0 := by
  let G := groupScheme n (CommRingCat.of k)
  let χ := Lie.adjointDeterminantCharacter G
  obtain ⟨m, hm⟩ := exists_characterOnAffineMatrices_power χ.toMul
  have heq : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (g : GL n A),
      characterOnAffineMatrices χ.toMul A g = 1 := by
    cases isEmpty_or_nonempty n with
    | inl hn =>
        let := hn
        exact fun A g => characterOnAffineMatrices_empty χ.toMul A g
    | inr hn =>
        have hscalar : characterOnAffineMatrices χ.toMul (CommAlgCat.of k k)
            (Matrix.GeneralLinearGroup.scalar n (Units.mk0 (2 : k) (by norm_num))) = 1 := by
          apply Units.ext
          rw [characterOnAffineMatrices_apply, Lie.adjointDeterminantCharacter_val,
            adjoint_scalar_eq_id, LinearMap.det_id]
          rfl
        rw [hm, Matrix.GeneralLinearGroup.det_scalar] at hscalar
        have hp : (2 : k) ^ ((Fintype.card n : ℤ) * m) = 1 := by
          simpa only [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
            ← zpow_natCast, ← zpow_mul] using congrArg Units.val hscalar
        have hpq : (2 : ℚ) ^ ((Fintype.card n : ℤ) * m) = 1 := by
          apply Rat.cast_injective (α := k)
          simpa only [Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_one] using hp
        have hm0 : m = 0 := by
          have := (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℚ) ≤ 2)
            (by norm_num : (2 : ℚ) ≠ 1)).mp hpq
          exact (mul_eq_zero.mp this).resolve_left (by
            exact_mod_cast (Fintype.card_ne_zero : Fintype.card n ≠ 0))
        intro A g
        rw [hm, hm0, zpow_zero]
  apply Additive.toMul.injective
  apply characterOnAffineMatrices_ext
  intro A g
  rw [heq]
  simp only [characterOnAffineMatrices_apply]
  rw [rationalCharacters.comp_zero, map_one]

end Langlands.GroupScheme.GeneralLinear
