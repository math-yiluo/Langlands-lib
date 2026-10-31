import Langlands.Automorphic.DeterminantMultiplier

/-! # Actual determinant multiplication between specified central-character spaces -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

@[simp]
theorem determinant_scalar (z : Ideles F) :
    determinant F n (scalar F n z) = z ^ n := by
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) z) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

end Langlands.Global.AdelicGL

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

@[simp]
theorem adelicDeterminant_scalar (χ : HeckeCharacter F) (z : Ideles F) :
    χ.adelicDeterminant n (AdelicGL.scalar F n z) = χ.onIdeles z ^ n := by
  change χ.onIdeles (AdelicGL.determinant F n (AdelicGL.scalar F n z)) = _
  rw [AdelicGL.determinant_scalar, map_pow]

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance centralMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance centralMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance centralMultiplierCentralGroup (ω : HeckeCharacter F) :
    AddCommGroup (CentralCharacterFunctions F n ω) := Submodule.addCommGroup _

/-- Multiplication by `χ(det g)` changes the central character from `ω` to `χ^n * ω`. -/
theorem centralCharacter_determinantMultiplier
    (χ ω : HeckeCharacter F) {f : ContinuousRationalFunctions F n}
    (hf : f ∈ centralCharacterSubrepresentation F n ω) :
    determinantMultiplier n χ f ∈ centralCharacterSubrepresentation F n (χ ^ n * ω) := by
  intro z x
  have hz : centralIdeleCharacter F (χ ^ n * ω) z =
      χ.onIdeles z ^ n * centralIdeleCharacter F ω z := by
    change (χ ^ n * ω) (ideleClassMap F z) =
      χ (ideleClassMap F z) ^ n * ω (ideleClassMap F z)
    simp only [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply]
  change (χ.adelicDeterminant n (AdelicGL.scalar F n z * x) : ℂ) *
      evaluate F n f (AdelicGL.scalar F n z * x) =
    (centralIdeleCharacter F (χ ^ n * ω) z : ℂ) *
      ((χ.adelicDeterminant n x : ℂ) * evaluate F n f x)
  rw [map_mul, Units.val_mul, hf z x, HeckeCharacter.adelicDeterminant_scalar,
    hz, Units.val_mul]
  ac_rfl

private theorem centralCharacter_map_determinantMultiplier
    (χ ω : HeckeCharacter F) :
    (centralCharacterSubrepresentation F n ω).toSubmodule.map
        (determinantMultiplier n χ).toLinearMap =
      (centralCharacterSubrepresentation F n (χ ^ n * ω)).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact centralCharacter_determinantMultiplier n χ ω hg
  · intro hf
    have hg := centralCharacter_determinantMultiplier n χ⁻¹ (χ ^ n * ω) hf
    have hi : (χ⁻¹) ^ n * (χ ^ n * ω) = ω := by
      rw [inv_pow]
      exact inv_mul_cancel_left (χ ^ n) ω
    rw [hi] at hg
    refine ⟨determinantMultiplier n χ⁻¹ f, hg, ?_⟩
    change determinantMul n χ (determinantMul n χ⁻¹ f) = f
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f

namespace CentralCharacterFunctions

/-- The actual continuous multiplier between the existing specified-character carriers. -/
def determinantMultiplier (χ ω : HeckeCharacter F) :
    CentralCharacterFunctions F n ω ≃L[ℂ] CentralCharacterFunctions F n (χ ^ n * ω) :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (centralCharacter_map_determinantMultiplier n χ ω)

@[simp]
theorem determinantMultiplier_val (χ ω : HeckeCharacter F)
    (f : CentralCharacterFunctions F n ω) :
    (determinantMultiplier n χ ω f).val =
      ContinuousRationalFunctions.determinantMultiplier n χ f.val := rfl

@[simp]
theorem evaluate_determinantMultiplier (χ ω : HeckeCharacter F)
    (f : CentralCharacterFunctions F n ω) (g : AdelicGL F n) :
    evaluate F n (determinantMultiplier n χ ω f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

@[simp]
theorem evaluate_determinantMultiplier_symm (χ ω : HeckeCharacter F)
    (f : CentralCharacterFunctions F n (χ ^ n * ω)) (g : AdelicGL F n) :
    evaluate F n ((determinantMultiplier n χ ω).symm f).val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val g := rfl

theorem rightAction_determinantMultiplier (χ ω : HeckeCharacter F)
    (g : AdelicGL F n) (f : CentralCharacterFunctions F n ω) :
    centralCharacterRightAction F n (χ ^ n * ω) g (determinantMultiplier n χ ω f) =
      (χ.adelicDeterminant n g : ℂ) •
        determinantMultiplier n χ ω (centralCharacterRightAction F n ω g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end CentralCharacterFunctions
end Langlands.Automorphic
