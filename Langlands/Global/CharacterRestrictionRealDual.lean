import Langlands.Global.AdelicCharacterLog
import Langlands.GroupScheme.Rational.Characters
import Mathlib.GroupTheory.OrderOfElement

/-! # Real duals of actual finite-index character restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
variable (G H : GroupScheme (Spec (CommRingCat.of F))) (i : H ⟶ G)

/-- Multiplication by the character-restriction index lands in its actual image. -/
def characterIndexMultiple : rationalCharacters H →+ (characterRestrict i).range where
  toFun ψ := ⟨(characterRestrict i).range.index • ψ,
    (characterRestrict i).range.nsmul_index_mem ψ⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' ψ ξ := Subtype.ext (nsmul_add ψ ξ _)

variable (hi : Function.Injective (characterRestrict i))

/-- The unique lift of index times each actual character through the injective restriction. -/
def characterIndexLift : rationalCharacters H →+ rationalCharacters G :=
  (AddMonoidHom.ofInjective hi).symm.toAddMonoidHom.comp (characterIndexMultiple F G H i)

@[simp] theorem restrict_characterIndexLift (ψ : rationalCharacters H) :
    characterRestrict i (characterIndexLift F G H i hi ψ) =
      (characterRestrict i).range.index • ψ :=
  AddMonoidHom.apply_ofInjective_symm hi _

@[simp] theorem characterIndexLift_restrict (χ : rationalCharacters G) :
    characterIndexLift F G H i hi (characterRestrict i χ) =
      (characterRestrict i).range.index • χ := by
  apply hi
  rw [restrict_characterIndexLift, map_nsmul]

/-- Extension of real functionals by the explicit index-normalized character lift. -/
def realCharacterDualExtend : RealCharacterDual F G →ₗ[ℝ] RealCharacterDual F H where
  toFun ℓ := ((characterRestrict i).range.index : ℝ)⁻¹ •
    (ℓ.comp (characterIndexLift F G H i hi) : rationalCharacters H →+ ℝ)
  map_add' ℓ m := by
    apply AddMonoidHom.ext
    intro ψ
    change _ * (ℓ _ + m _) = _ * ℓ _ + _ * m _
    exact mul_add _ _ _
  map_smul' r ℓ := by
    apply AddMonoidHom.ext
    intro ψ
    change _ * (r * ℓ _) = r * (_ * ℓ _)
    ring

@[simp] theorem realCharacterDualExtend_apply (ℓ : RealCharacterDual F G)
    (ψ : rationalCharacters H) :
    realCharacterDualExtend F G H i hi ℓ ψ =
      ((characterRestrict i).range.index : ℝ)⁻¹ * ℓ (characterIndexLift F G H i hi ψ) := rfl

theorem continuous_realCharacterDualExtend :
    Continuous (realCharacterDualExtend F G H i hi) :=
  continuous_induced_rng.mpr (continuous_pi fun ψ =>
    continuous_const.mul (continuous_dualEval F G (characterIndexLift F G H i hi ψ)))

variable [(characterRestrict i).range.FiniteIndex]

/-- Finite index makes the normalization factor nonzero. -/
theorem characterRestrictionIndex_ne_zero :
    ((characterRestrict i).range.index : ℝ) ≠ 0 := by
  exact_mod_cast (AddSubgroup.FiniteIndex.index_ne_zero (H := (characterRestrict i).range))

/-- Restriction followed by explicit extension recovers every real functional on `G`. -/
theorem realCharacterDualMap_extend (ℓ : RealCharacterDual F G) :
    realCharacterDualMap F H G i (realCharacterDualExtend F G H i hi ℓ) = ℓ := by
  apply AddMonoidHom.ext
  intro χ
  change ((characterRestrict i).range.index : ℝ)⁻¹ *
    ℓ (characterIndexLift F G H i hi (characterRestrict i χ)) = ℓ χ
  rw [characterIndexLift_restrict]
  let l : rationalCharacters G →+ ℝ := ℓ
  change _ * l (_ • χ) = l χ
  rw [map_nsmul, nsmul_eq_mul, inv_mul_cancel_left₀ (characterRestrictionIndex_ne_zero F G H i)]

/-- Explicit extension after restriction recovers every real functional on `H`. -/
theorem realCharacterDualExtend_map (ℓ : RealCharacterDual F H) :
    realCharacterDualExtend F G H i hi (realCharacterDualMap F H G i ℓ) = ℓ := by
  apply AddMonoidHom.ext
  intro ψ
  change ((characterRestrict i).range.index : ℝ)⁻¹ *
    ℓ (characterRestrict i (characterIndexLift F G H i hi ψ)) = ℓ ψ
  rw [restrict_characterIndexLift]
  let l : rationalCharacters H →+ ℝ := ℓ
  change _ * l (_ • ψ) = l ψ
  rw [map_nsmul, nsmul_eq_mul, inv_mul_cancel_left₀ (characterRestrictionIndex_ne_zero F G H i)]

/-- An injective finite-index actual character restriction induces a continuous real-linear
isomorphism of the entire real duals. Its forward map is the existing covariant dual map. -/
def realCharacterDualRestrictionEquiv : RealCharacterDual F H ≃L[ℝ] RealCharacterDual F G where
  toLinearEquiv :=
    { realCharacterDualMap F H G i with
      invFun := realCharacterDualExtend F G H i hi
      left_inv := realCharacterDualExtend_map F G H i hi
      right_inv := realCharacterDualMap_extend F G H i hi }
  continuous_toFun := continuous_realCharacterDualMap F H G i
  continuous_invFun := continuous_realCharacterDualExtend F G H i hi

@[simp] theorem realCharacterDualRestrictionEquiv_apply (ℓ : RealCharacterDual F H) :
    realCharacterDualRestrictionEquiv F G H i hi ℓ = realCharacterDualMap F H G i ℓ := rfl

@[simp] theorem realCharacterDualRestrictionEquiv_symm_apply (ℓ : RealCharacterDual F G) :
    (realCharacterDualRestrictionEquiv F G H i hi).symm ℓ =
      realCharacterDualExtend F G H i hi ℓ := rfl

end Langlands.Global.AdelicGroupPoints
