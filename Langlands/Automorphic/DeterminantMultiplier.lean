import Langlands.Automorphic.Ambient
import Langlands.Global.HeckeCharacter
import Mathlib.Topology.Algebra.Module.Equiv

/-! # Actual determinant multiplication on continuous adelic functions -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-- Pullback of an actual Hecke character along the adelic determinant. -/
def adelicDeterminant (χ : HeckeCharacter F) : AdelicGL F n →ₜ* ℂˣ :=
  χ.onIdeles.comp (AdelicGL.determinant F n)

@[simp]
theorem adelicDeterminant_rational (χ : HeckeCharacter F) (γ : RationalGL F n) :
    χ.adelicDeterminant n (AdelicGL.rational F n γ) = 1 := by
  change χ.onIdeles (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F)) γ)) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact χ.onIdeles_diagonalUnits (Matrix.GeneralLinearGroup.det γ)

@[simp]
theorem adelicDeterminant_inv (χ : HeckeCharacter F) (x : AdelicGL F n) :
    χ⁻¹.adelicDeterminant n x = (χ.adelicDeterminant n x)⁻¹ := rfl

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance determinantMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance determinantMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _

namespace ContinuousRationalFunctions

/-- Actual multiplication by `χ(det x)`, including rational invariance and continuity. -/
def determinantMul (χ : HeckeCharacter F) :
    ContinuousRationalFunctions F n →ₗ[ℂ] ContinuousRationalFunctions F n where
  toFun f :=
    ⟨⟨fun x => (χ.adelicDeterminant n x : ℂ) * evaluate F n f x, by
      intro γ x
      change (χ.adelicDeterminant n (AdelicGL.rational F n γ * x) : ℂ) *
        evaluate F n f (AdelicGL.rational F n γ * x) =
          (χ.adelicDeterminant n x : ℂ) * evaluate F n f x
      rw [map_mul, HeckeCharacter.adelicDeterminant_rational, one_mul,
        evaluate_rational]⟩,
      (Units.continuous_val.comp (χ.adelicDeterminant n).continuous).mul
        (continuous_evaluate F n f)⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change _ * (c * _) = c * (_ * _)
    ac_rfl

@[simp]
theorem evaluate_determinantMul (χ : HeckeCharacter F)
    (f : ContinuousRationalFunctions F n) (x : AdelicGL F n) :
    evaluate F n (determinantMul n χ f) x =
      (χ.adelicDeterminant n x : ℂ) * evaluate F n f x := rfl

private theorem continuous_fixedMultiplier {X : Type*} [TopologicalSpace X]
    (m : C(X, ℂ)) : Continuous (fun f : C(X, ℂ) => m * f) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply (ContinuousMap.tendsto_compactOpen_iff_forall _ _).mpr
  intro K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  change Filter.Tendsto (fun g : C(X, ℂ) => m.restrict K * g.restrict K)
    (nhds f) (nhds (m.restrict K * f.restrict K))
  exact (continuous_const.mul (ContinuousMap.continuous_restrict K)).continuousAt

theorem continuous_determinantMul (χ : HeckeCharacter F) :
    Continuous (determinantMul n χ) := by
  rw [continuous_induced_rng]
  let m : C(AdelicGL F n, ℂ) :=
    ⟨fun x => (χ.adelicDeterminant n x : ℂ),
      Units.continuous_val.comp (χ.adelicDeterminant n).continuous⟩
  exact (continuous_fixedMultiplier m).comp
    (show Continuous (toContinuousMap F n) from continuous_induced_dom)

theorem determinantMul_inv_apply (χ : HeckeCharacter F)
    (f : ContinuousRationalFunctions F n) :
    determinantMul n χ⁻¹ (determinantMul n χ f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (((χ.adelicDeterminant n x)⁻¹ : ℂˣ) : ℂ) *
    ((χ.adelicDeterminant n x : ℂ) * evaluate F n f x) = evaluate F n f x
  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- A continuous complex-linear automorphism with inverse multiplication by `χ⁻¹`. -/
def determinantMultiplier (χ : HeckeCharacter F) :
    ContinuousRationalFunctions F n ≃L[ℂ] ContinuousRationalFunctions F n where
  __ := determinantMul n χ
  invFun := determinantMul n χ⁻¹
  left_inv := determinantMul_inv_apply n χ
  right_inv f := by
    change determinantMul n χ (determinantMul n χ⁻¹ f) = f
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f
  continuous_toFun := continuous_determinantMul n χ
  continuous_invFun := continuous_determinantMul n χ⁻¹

@[simp]
theorem evaluate_determinantMultiplier (χ : HeckeCharacter F)
    (f : ContinuousRationalFunctions F n) (x : AdelicGL F n) :
    evaluate F n (determinantMultiplier n χ f) x =
      (χ.adelicDeterminant n x : ℂ) * evaluate F n f x := rfl

/-- Right translation transforms by the same determinant character. -/
theorem determinantMultiplier_rightAction (χ : HeckeCharacter F)
    (g : AdelicGL F n) (f : ContinuousRationalFunctions F n) :
    continuousRightAction F n g (determinantMultiplier n χ f) =
      (χ.adelicDeterminant n g : ℂ) •
        determinantMultiplier n χ (continuousRightAction F n g f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (χ.adelicDeterminant n (x * g) : ℂ) * evaluate F n f (x * g) =
    (χ.adelicDeterminant n g : ℂ) *
      ((χ.adelicDeterminant n x : ℂ) * evaluate F n f (x * g))
  rw [map_mul, Units.val_mul]
  ac_rfl

end ContinuousRationalFunctions
end Langlands.Automorphic
