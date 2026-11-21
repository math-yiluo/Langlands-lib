import Langlands.Global.AdelicCharacterParameterPullback
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual character duality and finite-index parameter restriction -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicGroupPoints

open GroupScheme Langlands.LinearAlgebra

variable {F : Type u} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The inverse of scalar extension of a character functional, defined by evaluation at
`1 ⊗ χ`. -/
def parameterDualOnCharacters :
    Module.Dual ℝ (RealCharacterParameter F G) →ₗ[ℝ] RealCharacterDual F G where
  toFun l := l.toAddMonoidHom.comp ((TensorProduct.mk ℤ ℝ (rationalCharacters G)) 1).toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem parameterDualOnCharacters_apply (l : Module.Dual ℝ (RealCharacterParameter F G))
    (χ : rationalCharacters G) : parameterDualOnCharacters l χ = l ((1 : ℝ) ⊗ₜ[ℤ] χ) := rfl

/-- The real logarithmic character dual identifies with the algebraic real-linear dual of the
actual real parameter space. The equivalence is precisely the existing pairing with arguments
flipped. -/
def realCharacterDualEquivParameterDual :
    RealCharacterDual F G ≃ₗ[ℝ] Module.Dual ℝ (RealCharacterParameter F G) :=
  LinearEquiv.ofLinearMap (realParameterPairing F G).flip parameterDualOnCharacters
    (by
      apply LinearMap.ext
      intro l
      apply AlgebraTensorModule.ext
      intro t χ
      change t * l ((1 : ℝ) ⊗ₜ[ℤ] χ) = l (t ⊗ₜ[ℤ] χ)
      rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (by
      apply LinearMap.ext
      intro l
      apply AddMonoidHom.ext
      intro χ
      change 1 * l χ = l χ
      exact one_mul _)

@[simp] theorem realCharacterDualEquivParameterDual_apply (h : RealCharacterDual F G)
    (x : RealCharacterParameter F G) :
    realCharacterDualEquivParameterDual h x = realParameterPairing F G x h := rfl

/-- The actual real character dual separates the real parameters. -/
theorem realParameterPairing_eq_zero_iff (x : RealCharacterParameter F G) :
    (∀ h, realParameterPairing F G x h = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff ℝ x).mp
    intro l
    obtain ⟨v, rfl⟩ := realCharacterDualEquivParameterDual.surjective l
    exact h v
  · rintro rfl h
    rw [map_zero, LinearMap.zero_apply]

/-- Injective finite-index restriction of actual rational characters becomes a real-linear
parameter equivalence. This is the real scalar extension of the rationalized restriction. -/
def realCharacterParameterPullbackEquiv (i : H ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    (hindex : (characterRestrict i).range.FiniteIndex) :
    RealCharacterParameter F G ≃ₗ[ℝ] RealCharacterParameter F H :=
  (rationalRealTensorEquiv (rationalCharacters G)).symm.trans
    (((LinearEquiv.ofBijective (rationalCharacterRestrictRat i)
      (rationalCharacterRestrictRat_bijective_of_integralRestriction i hi hindex)).baseChange ℚ ℝ _ _).trans
      (rationalRealTensorEquiv (rationalCharacters H)))

@[simp] theorem realCharacterParameterPullbackEquiv_apply (i : H ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    (hindex : (characterRestrict i).range.FiniteIndex) (x : RealCharacterParameter F G) :
    realCharacterParameterPullbackEquiv i hi hindex x = realCharacterParameterPullback i x := by
  let f := (characterRestrict i).toIntLinearMap
  let y := (rationalRealTensorEquiv (rationalCharacters G)).symm x
  have h := LinearMap.congr_fun (rationalRealTensorEquiv_naturality f) y
  change rationalRealTensorEquiv (rationalCharacters H) ((f.baseChange ℚ).baseChange ℝ y) =
    f.baseChange ℝ (rationalRealTensorEquiv (rationalCharacters G) y) at h
  rw [show rationalRealTensorEquiv (rationalCharacters G) y = x from LinearEquiv.apply_symm_apply _ _] at h
  exact h

end Langlands.Global.AdelicGroupPoints
