import Langlands.Global.AdelicCharacterLog
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Complex character parameters and the adelic characters `m ↦ m^λ`

Bernstein–Lapid §2.1 and Mœglin–Waldspurger I.1.4: over a number field the
parameter space of a group `G` is `𝔛 = X^*(G) ⊗ ℂ`, it pairs with
`𝔞 = Hom(X^*(G), ℝ)`, and `λ ∈ 𝔛` defines the character
`m ↦ m^λ = exp ⟨λ, H_G(m)⟩` of `G(𝔸)`, where `H_G` is the normalized
logarithmic map `characterLog`. -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The complex parameter space `𝔛 = X^*(G) ⊗_ℤ ℂ` of the actual group `G`,
written with the complex scalars as first tensor factor. -/
abbrev ComplexCharacterParameter := ℂ ⊗[ℤ] GroupScheme.rationalCharacters G

/-- The real parameter space `𝔞^* = X^*(G) ⊗_ℤ ℝ`, with the real scalars as
first tensor factor. -/
abbrev RealCharacterParameter := ℝ ⊗[ℤ] GroupScheme.rationalCharacters G

/-- Evaluation of a real dual element `H ∈ Hom(X^*(G), ℝ)` at a rational
character `χ`, as a complex-valued real-linear form in `H` depending
additively on `χ`. -/
def complexCharacterEvaluation :
    GroupScheme.rationalCharacters G →ₗ[ℤ] (RealCharacterDual F G →ₗ[ℝ] ℂ) :=
  (show GroupScheme.rationalCharacters G →+ (RealCharacterDual F G →ₗ[ℝ] ℂ) from
    { toFun := fun χ => Complex.ofRealCLM.toLinearMap ∘ₗ dualEval F G χ
      map_zero' := by
        ext H
        change ((H 0 : ℝ) : ℂ) = 0
        rw [show H 0 = 0 from AddMonoidHom.map_zero (H : GroupScheme.rationalCharacters G →+ ℝ),
          Complex.ofReal_zero]
      map_add' := fun χ ψ => by
        ext H
        change ((H (χ + ψ) : ℝ) : ℂ) = (H χ : ℂ) + (H ψ : ℂ)
        rw [show H (χ + ψ) = H χ + H ψ from
          AddMonoidHom.map_add (H : GroupScheme.rationalCharacters G →+ ℝ) χ ψ,
          Complex.ofReal_add] }).toIntLinearMap

/-- Evaluation of a real dual element at a rational character, as a real-valued
real-linear form depending additively on the character. -/
def realCharacterEvaluation :
    GroupScheme.rationalCharacters G →ₗ[ℤ] (RealCharacterDual F G →ₗ[ℝ] ℝ) :=
  (show GroupScheme.rationalCharacters G →+ (RealCharacterDual F G →ₗ[ℝ] ℝ) from
    { toFun := fun χ => dualEval F G χ
      map_zero' := by
        ext H
        exact AddMonoidHom.map_zero (H : GroupScheme.rationalCharacters G →+ ℝ)
      map_add' := fun χ ψ => by
        ext H
        exact AddMonoidHom.map_add (H : GroupScheme.rationalCharacters G →+ ℝ) χ ψ }).toIntLinearMap

/-- The complex pairing `⟨λ, H⟩` of `λ ∈ X^*(G) ⊗ ℂ` with `H ∈ Hom(X^*(G), ℝ)`:
`⟨s ⊗ χ, H⟩ = s · H(χ)`. -/
def complexParameterPairing :
    ComplexCharacterParameter F G →ₗ[ℂ] (RealCharacterDual F G →ₗ[ℝ] ℂ) :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ
      (GroupScheme.rationalCharacters G →ₗ[ℤ] (RealCharacterDual F G →ₗ[ℝ] ℂ))
      (complexCharacterEvaluation F G))

omit [NumberField F] in
@[simp]
theorem complexParameterPairing_tmul (s : ℂ) (χ : GroupScheme.rationalCharacters G)
    (H : RealCharacterDual F G) :
    complexParameterPairing F G (s ⊗ₜ[ℤ] χ) H = s * (H χ : ℂ) := rfl

/-- The real pairing `⟨μ, H⟩` of `μ ∈ X^*(G) ⊗ ℝ` with `H ∈ Hom(X^*(G), ℝ)`:
`⟨t ⊗ χ, H⟩ = t · H(χ)`. -/
def realParameterPairing :
    RealCharacterParameter F G →ₗ[ℝ] (RealCharacterDual F G →ₗ[ℝ] ℝ) :=
  AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ
      (GroupScheme.rationalCharacters G →ₗ[ℤ] (RealCharacterDual F G →ₗ[ℝ] ℝ))
      (realCharacterEvaluation F G))

omit [NumberField F] in
@[simp]
theorem realParameterPairing_tmul (t : ℝ) (χ : GroupScheme.rationalCharacters G)
    (H : RealCharacterDual F G) :
    realParameterPairing F G (t ⊗ₜ[ℤ] χ) H = t * H χ := rfl

/-- The real part `Re : X^*(G) ⊗ ℂ → X^*(G) ⊗ ℝ`, the real part of the scalar
factor. -/
def parameterRealPart : ComplexCharacterParameter F G →ₗ[ℝ] RealCharacterParameter F G :=
  AlgebraTensorModule.map Complex.reLm LinearMap.id

omit [NumberField F] in
@[simp]
theorem parameterRealPart_tmul (s : ℂ) (χ : GroupScheme.rationalCharacters G) :
    parameterRealPart F G (s ⊗ₜ[ℤ] χ) = s.re ⊗ₜ[ℤ] χ := rfl

/-- The complex number `m^λ = exp ⟨λ, H_G(m)⟩` for an actual adelic point `m`
of `G` and `λ ∈ X^*(G) ⊗ ℂ`. -/
def parameterPower (lam : ComplexCharacterParameter F G) (m : AdelicGroupPoints F G) : ℂ :=
  Complex.exp (complexParameterPairing F G lam (characterLog F G m))

/-- The character `m ↦ m^λ` of the actual adelic points of `G` with values in
`ℂˣ` (Bernstein–Lapid §2.1). -/
def parameterCharacter (lam : ComplexCharacterParameter F G) :
    AdelicGroupPoints F G →* ℂˣ where
  toFun m := Units.mk0 (parameterPower F G lam m) (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp [parameterPower, characterLog_one]
  map_mul' m m' := by
    ext
    simp [parameterPower, characterLog_mul, Complex.exp_add]

@[simp]
theorem parameterCharacter_apply (lam : ComplexCharacterParameter F G)
    (m : AdelicGroupPoints F G) :
    (parameterCharacter F G lam m : ℂ) = parameterPower F G lam m := rfl

end Langlands.Global.AdelicGroupPoints
