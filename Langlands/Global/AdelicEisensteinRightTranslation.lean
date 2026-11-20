import Langlands.Global.AdelicEisensteinSeries
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Whittaker.Algebraic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Parameter-dependent right translation of Eisenstein sections -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.AdelicGroupPoints

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

namespace IsIwasawaCompact

theorem heightPower_ne_zero (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower lam g ≠ 0 :=
  Complex.exp_ne_zero _

/-- Twisting is a linear equivalence on scalar functions, with inverse given
by division by the nonzero height power. -/
def parameterTwistEquiv (lam : ComplexCharacterParameter F P) :
    (AdelicGroupPoints F G → ℂ) ≃ₗ[ℂ] (AdelicGroupPoints F G → ℂ) where
  toFun φ := hK.parameterTwist φ lam
  invFun φ g := φ g / hK.heightPower lam g
  left_inv φ := funext fun g => mul_div_cancel_right₀ (φ g) (hK.heightPower_ne_zero lam g)
  right_inv φ := funext fun g => div_mul_cancel₀ (φ g) (hK.heightPower_ne_zero lam g)
  map_add' φ ψ := funext fun g => add_mul (φ g) (ψ g) _
  map_smul' c φ := funext fun g => mul_assoc c (φ g) _

/-- Transport positive right translation to the fixed untwisted carrier
through the twist at `lam`. -/
def parameterRightAction (lam : ComplexCharacterParameter F P) :
    Representation ℂ (AdelicGroupPoints F G) (AdelicGroupPoints F G → ℂ) :=
  transportRepresentation (Whittaker.rightTranslation ℂ (AdelicGroupPoints F G))
    (hK.parameterTwistEquiv lam).symm

theorem parameterRightAction_apply (lam : ComplexCharacterParameter F P)
    (d : AdelicGroupPoints F G) (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.parameterRightAction lam d φ g = φ (g * d) *
      hK.heightPower lam (g * d) / hK.heightPower lam g :=
  rfl

theorem parameterTwist_parameterRightAction (lam : ComplexCharacterParameter F P)
    (d : AdelicGroupPoints F G) (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.parameterTwist (hK.parameterRightAction lam d φ) lam g =
      hK.parameterTwist φ lam (g * d) :=
  div_mul_cancel₀ _ (hK.heightPower_ne_zero lam g)

section Iwasawa

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]

/-- On the Iwasawa compact subgroup, the untwisted translation is independent
of the parameter. -/
theorem parameterRightAction_compact (lam : ComplexCharacterParameter F P)
    (d : AdelicGroupPoints F G) (hd : d ∈ K)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.parameterRightAction lam d φ g = φ (g * d) := by
  have h : hK.heightPower lam (g * d) = hK.heightPower lam g := by
    unfold heightPower
    rw [hK.height_mul_right g hd]
  rw [parameterRightAction_apply, h, mul_div_cancel_right₀ _ (hK.heightPower_ne_zero lam g)]

/-- The deformed right action preserves left rational parabolic invariance. -/
theorem parameterRightAction_rational_mul (lam : ComplexCharacterParameter F P)
    (d : AdelicGroupPoints F G) (φ : AdelicGroupPoints F G → ℂ)
    (γ : RationalGroupPoints F P)
    (hφ : ∀ g, φ (map F P G p (rational F P γ) * g) = φ g) (g : AdelicGroupPoints F G) :
    hK.parameterRightAction lam d φ (map F P G p (rational F P γ) * g) =
      hK.parameterRightAction lam d φ g := by
  simp only [parameterRightAction_apply, mul_assoc, hφ, heightPower, hK.height_rational_mul γ]

end Iwasawa

/-- The actual Eisenstein sum intertwines this deformed right translation with
ordinary right translation, term by term. -/
theorem eisensteinSeries_parameterRightAction (lam : ComplexCharacterParameter F P)
    (d : AdelicGroupPoints F G) (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries (hK.parameterRightAction lam d φ) lam g =
      hK.eisensteinSeries φ lam (g * d) := by
  unfold eisensteinSeries
  apply tsum_congr
  intro c
  simp only [eisensteinTerm, parameterTwist_parameterRightAction, mul_assoc]

/-- For a fixed section and evaluation point, the deformed translate is
holomorphic along every affine complex parameter line. -/
theorem analyticAt_parameterRightAction_line
    (lam mu : ComplexCharacterParameter F P) (t₀ : ℂ)
    (d : AdelicGroupPoints F G) (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    AnalyticAt ℂ (fun t : ℂ => hK.parameterRightAction (lam + t • mu) d φ g) t₀ := by
  have hpow (x : AdelicGroupPoints F G) :
      AnalyticAt ℂ (fun t : ℂ => hK.heightPower (lam + t • mu) x) t₀ := by
    simp only [heightPower, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    fun_prop
  simp only [parameterRightAction_apply]
  exact (analyticAt_const.mul (hpow (g * d))).div (hpow g) (hK.heightPower_ne_zero _ g)

end IsIwasawaCompact

end Langlands.Global.AdelicGroupPoints
