import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.AdelicComplexParameters

/-! # Pullback of actual character parameters

Scalar extension of rational character restriction along a group-scheme morphism, with
naturality for the real and complex pairings against the logarithmic character dual.
-/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {P G B : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- Pull back real character parameters along `p`, by extending rational character restriction
from `ℤ` to `ℝ`. -/
def realCharacterParameterPullback (p : P ⟶ G) :
    RealCharacterParameter F G →ₗ[ℝ] RealCharacterParameter F P :=
  AlgebraTensorModule.map LinearMap.id (GroupScheme.characterRestrict p).toIntLinearMap

omit [NumberField F] in
@[simp] theorem realCharacterParameterPullback_tmul (p : P ⟶ G) (t : ℝ)
    (χ : GroupScheme.rationalCharacters G) :
    realCharacterParameterPullback p (t ⊗ₜ[ℤ] χ) = t ⊗ₜ[ℤ] GroupScheme.characterRestrict p χ :=
  rfl

omit [NumberField F] in
@[simp] theorem complexCharacterParameterPullback_tmul (p : P ⟶ G) (z : ℂ)
    (χ : GroupScheme.rationalCharacters G) :
    parameterRestrict p (z ⊗ₜ[ℤ] χ) = z ⊗ₜ[ℤ] GroupScheme.characterRestrict p χ :=
  rfl

omit [NumberField F] in
@[simp] theorem realCharacterParameterPullback_id :
    realCharacterParameterPullback (𝟙 G) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro t χ
  simp [GroupScheme.characterRestrict_id]

omit [NumberField F] in
@[simp] theorem complexCharacterParameterPullback_id :
    parameterRestrict (𝟙 G) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro z χ
  simp [GroupScheme.characterRestrict_id]

omit [NumberField F] in
/-- The real pullbacks compose contravariantly. -/
theorem realCharacterParameterPullback_comp (p : P ⟶ G) (b : B ⟶ P) :
    realCharacterParameterPullback (b ≫ p) =
      (realCharacterParameterPullback b).comp (realCharacterParameterPullback p) := by
  apply AlgebraTensorModule.ext
  intro t χ
  simp [GroupScheme.characterRestrict_comp]

omit [NumberField F] in
/-- The complex pullbacks compose contravariantly. -/
theorem complexCharacterParameterPullback_comp (p : P ⟶ G) (b : B ⟶ P) :
    parameterRestrict (b ≫ p) =
      (parameterRestrict b).comp (parameterRestrict p) := by
  apply AlgebraTensorModule.ext
  intro z χ
  simp [GroupScheme.characterRestrict_comp]

omit [NumberField F] in
/-- Pullback on parameters is adjoint to the covariant map on real character duals. -/
theorem realParameterPairing_pullback (p : P ⟶ G) (mu : RealCharacterParameter F G)
    (H : RealCharacterDual F P) :
    realParameterPairing F P (realCharacterParameterPullback p mu) H =
      realParameterPairing F G mu (realCharacterDualMap F P G p H) := by
  induction mu using TensorProduct.inductionOn with
  | tmul t χ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

omit [NumberField F] in
/-- Taking the real part commutes with pullback of character parameters. -/
theorem parameterRealPart_pullback (p : P ⟶ G) (ν : ComplexCharacterParameter F G) :
    parameterRealPart F P (parameterRestrict p ν) =
      realCharacterParameterPullback p (parameterRealPart F G ν) := by
  induction ν using TensorProduct.inductionOn with
  | tmul z χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Evaluating the character of a pulled-back parameter equals evaluation after mapping the
actual adelic point. -/
theorem parameterPower_pullback (p : P ⟶ G) (ν : ComplexCharacterParameter F G)
    (x : AdelicGroupPoints F P) :
    parameterPower F P (parameterRestrict p ν) x =
      parameterPower F G ν (map F P G p x) := by
  simp only [parameterPower, complexParameterPairing_parameterRestrict, characterLog_map]

end Langlands.Global.AdelicGroupPoints
