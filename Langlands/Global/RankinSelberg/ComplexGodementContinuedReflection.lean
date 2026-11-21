import Langlands.Global.RankinSelberg.ComplexGodementRecursionBridge
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerDual
import Langlands.Representation.Archimedean.ComplexPermutationSwap

/-! # Reflection of the continued complex Godement value -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter

open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure)
open Langlands.GeneralLinear Langlands.GodementJacquet
open Langlands.HarmonicAnalysis (unipotentFourierSum)
open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.LocalFactor.Archimedean
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "smaller" => r + 1
local notation "larger" => r + 1 + 1
local notation "H" => Langlands.GeneralLinear smaller ℂ
local notation "G" => Langlands.GeneralLinear larger ℂ
local notation "Rect" => Matrix (Fin smaller) (Fin larger) ℂ
local notation "dualH" => ArchimedeanLocal.dualFunction smaller
local notation "dualG" => ArchimedeanLocal.dualFunction larger

private theorem invCharacter_eq (d : ComplexCharacterData) :
    d.inv.character.toMonoidHom = d.character.toMonoidHom.comp invMonoidHom := by
  ext z
  change (d.inv.character z : ℂ) = (d.character z⁻¹ : ℂ)
  rw [ComplexCharacterData.inv_character_apply, map_inv, Units.val_inv_eq_inv_val]

private theorem continuedValue_reflect_zero (D : ComplexQuotientMeasureData r) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ Ψ : 𝓢(Rect, ℂ))
    (hΨ : (Ψ : Rect → ℂ) = complexRectangularFourier a Φ)
    (ds : List ComplexCharacterData) (hds : ds.length = smaller)
    (W : complexWhittakerModel r ds (-a)) (g : G) :
    continuedValue D.groupHaar (complexSelfDualMeasure a) d a Φ W.val
      (weylInverseTranspose larger ℂ g) 0 =
      (d.character ((-1 : ℂˣ) ^ smaller) : ℂ) *
        continuedValue D.groupHaar (complexSelfDualMeasure a) d.inv (-a) Ψ (dualH W.val) g 0 := by
  let Wd : complexWhittakerModel r (dualData ds) (-(-a)) :=
    ⟨dualH W.val, dualFunction_mem hds W.2⟩
  have hW (u : Langlands.GeneralLinear.upperUnipotent smaller ℂ) (x : H) :
      W.val (u.val * x) = traceCharacter (-a) (unipotentFourierSum r u) * W.val x :=
    complexWhittakerModel_left_equivariant W.2 u.val u.2 x
  have hp := complexGodementRecursionBridge D a d Φ ds W (weylInverseTranspose larger ℂ g)
  have hd := complexGodementRecursionBridge D (-a) d.inv Ψ (dualData ds) Wd g
  have hdual := complexJacquetRecursion_dual (-a) D Φ W.val d.character.toMonoidHom hW g
  have hsign : (d.inv.character ((-1 : ℂˣ) ^ smaller) : ℂ) =
      (d.character ((-1 : ℂˣ) ^ smaller) : ℂ) := by
    change (d.inv.character.toMonoidHom ((-1 : ℂˣ) ^ smaller) : ℂ) = _
    rw [invCharacter_eq]
    change (d.character (((-1 : ℂˣ) ^ smaller)⁻¹) : ℂ) = _
    rw [← inv_pow, inv_neg, inv_one]
  rw [complexSelfDualMeasure_neg_scale, hsign, hΨ, invCharacter_eq] at hd
  rw [neg_neg, ← Units.val_pow_eq_pow_val, ← map_pow] at hdual
  rw [hp, hdual]
  have hWd : Langlands.Whittaker.dualFunction r W.val = Wd.val := by
    funext x
    rfl
  have hc : (d.character.toMonoidHom ((-1 : ℂˣ) ^ smaller) : ℂ) =
      (d.character ((-1 : ℂˣ) ^ smaller) : ℂ) := rfl
  rw [hWd, hc]
  change _ = (d.character ((-1 : ℂˣ) ^ smaller) : ℂ) *
    continuedValue D.groupHaar (complexSelfDualMeasure a) d.inv (-a) Ψ Wd.val g 0
  simpa only [neg_neg] using congrArg ((d.character ((-1 : ℂˣ) ^ smaller) : ℂ) * ·) hd.symm

private theorem shifted_inv (d : ComplexCharacterData) (p : ℂ) :
    (characterOfParams d.weight (d.exponent + p)).inv =
      characterOfParams d.inv.weight (d.inv.exponent + (-p)) := by
  apply Langlands.Archimedean.ComplexPermutation.eq_of_params
  · simp only [ComplexCharacterData.inv_weight, characterOfParams_weight]
  · simp only [ComplexCharacterData.inv_exponent, characterOfParams_exponent, neg_add]

/-- Weyl inverse transpose sends the continued column value to the continued value of the
rectangular Fourier transform with the dual smaller vector and inverse adjoining character. -/
def ComplexGodementContinuedReflectionStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (a : ℂˣ) (d : ComplexCharacterData)
    (Φ Ψ : 𝓢(Rect, ℂ)), (Ψ : Rect → ℂ) = complexRectangularFourier a Φ →
  ∀ (ds : List ComplexCharacterData), ds.length = smaller →
  ∀ (W : complexWhittakerModel r ds (-a)) (g : G) (p : ℂ),
    dualG (fun x => continuedValue D.groupHaar (complexSelfDualMeasure a) d a Φ W.val x p) g =
      (d.character ((-1 : ℂˣ) ^ smaller) : ℂ) *
        continuedValue D.groupHaar (complexSelfDualMeasure a) d.inv (-a) Ψ (dualH W.val) g (-p)

theorem complexGodementContinuedReflection : ComplexGodementContinuedReflectionStatement (r := r) := by
  intro D a d Φ Ψ hΨ ds hds W g p
  change continuedValue D.groupHaar (complexSelfDualMeasure a) d a Φ W.val
      (weylInverseTranspose larger ℂ g) p =
      (d.character ((-1 : ℂˣ) ^ smaller) : ℂ) *
        continuedValue D.groupHaar (complexSelfDualMeasure a) d.inv (-a) Ψ (dualH W.val) g (-p)
  rw [continuedValue_eq_shiftedCharacter, continuedValue_eq_shiftedCharacter
    D.groupHaar (complexSelfDualMeasure a) d.inv, ← shifted_inv]
  simpa only [shifted_character_sign] using
    continuedValue_reflect_zero D a (characterOfParams d.weight (d.exponent + p)) Φ Ψ hΨ ds hds W g

end Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter
