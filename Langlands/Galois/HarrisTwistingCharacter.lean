import Langlands.Global.HeckeNormPower
import Langlands.Global.HeckeCharacterTransport
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Galois.HeckeCharacterRealization

/-!
# Harris's twisting characters `ν(Gπ)` and `ν̄(π)`

Harris 1998, Erratum (E.1)--(E.2): for a Hecke character `ξ₀` of a number
field `𝒦₀` with an algebra map `𝒦₀ → 𝒦` (Harris: an imaginary quadratic
subfield) and `n : ℕ`, the Hecke character
`ν(a) = ξ₀(N_{𝒦/𝒦₀}(a))⁻¹ · ‖a‖^{(n-1)/2}` of `𝒦`, and, for a CM field `𝒦`,
its conjugate `ν̄(a) = ξ₀(N_{𝒦/𝒦₀}(c(a)))⁻¹ · ‖a‖^{(n-1)/2}`. Harris 1999,
(5.4) and Theorem 5.7, calls the latter `ν̄(π)`. Also the relation saying that
a `λ`-adic character realizes `ν̄`.
-/

noncomputable section

universe u u₀ uL

namespace Langlands.Global.Harris

open Langlands.Global AdelicFunctoriality
open NumberField (IsCMField)

variable {𝒦 : Type u} [Field 𝒦] [NumberField 𝒦]
variable {𝒦₀ : Type u₀} [Field 𝒦₀] [NumberField 𝒦₀] [Algebra 𝒦₀ 𝒦]

/-- Harris 1998, Erratum (E.1): `ν(a) = ξ₀(N_{𝒦/𝒦₀}(a))⁻¹ · ‖a‖^{(n-1)/2}`,
with the actual idele-class norm and the normalized idelic norm of `𝒦`. -/
def nuCharacter (n : ℕ) (ξ₀ : HeckeCharacter 𝒦₀) : HeckeCharacter 𝒦 :=
  (ξ₀.comp (ideleClassNorm (K := 𝒦₀) (L := 𝒦)))⁻¹ *
    HeckeCharacter.normPower 𝒦 (((n : ℂ) - 1) / 2)

theorem nuCharacter_apply (n : ℕ) (ξ₀ : HeckeCharacter 𝒦₀) (a : IdeleClasses 𝒦) :
    nuCharacter n ξ₀ a =
      (ξ₀ (ideleClassNorm (K := 𝒦₀) (L := 𝒦) a))⁻¹ *
        HeckeCharacter.normPower 𝒦 (((n : ℂ) - 1) / 2) a :=
  rfl

/-- Harris 1998, Erratum (E.1) with `r̄_μ = r_μ ∘ c` from (E.2):
`ν̄(a) = ξ₀(N_{𝒦/𝒦₀}(c(a)))⁻¹ · ‖a‖^{(n-1)/2}`, where `c` is complex conjugation
of the CM field `𝒦` acting on idele classes. This is Harris 1999's `ν̄(π)`. -/
def nuBarCharacter [IsCMField 𝒦] (n : ℕ) (ξ₀ : HeckeCharacter 𝒦₀) : HeckeCharacter 𝒦 :=
  (HeckeCharacter.complexConj (ξ₀.comp (ideleClassNorm (K := 𝒦₀) (L := 𝒦))))⁻¹ *
    HeckeCharacter.normPower 𝒦 (((n : ℂ) - 1) / 2)

theorem nuBarCharacter_apply [IsCMField 𝒦] (n : ℕ) (ξ₀ : HeckeCharacter 𝒦₀)
    (a : IdeleClasses 𝒦) :
    nuBarCharacter n ξ₀ a =
      (ξ₀ (ideleClassNorm (K := 𝒦₀) (L := 𝒦) (ideleClassComplexConj a)))⁻¹ *
        HeckeCharacter.normPower 𝒦 (((n : ℂ) - 1) / 2) a :=
  rfl

/-- Both characters differ only in the norm-composed factor. -/
theorem nuBarCharacter_eq [IsCMField 𝒦] (n : ℕ) (ξ₀ : HeckeCharacter 𝒦₀) :
    nuBarCharacter n ξ₀ =
      (HeckeCharacter.complexConj (ξ₀.comp (ideleClassNorm (K := 𝒦₀) (L := 𝒦))))⁻¹ *
        (ξ₀.comp (ideleClassNorm (K := 𝒦₀) (L := 𝒦))) * nuCharacter n ξ₀ := by
  rw [nuBarCharacter, nuCharacter, mul_assoc _ (ξ₀.comp _), mul_inv_cancel_left]

/-- The complex values of `ν̄` as numbers:
`ν̄(a) = ξ₀(N(c(a)))⁻¹ · exp(((n-1)/2) · log ‖a‖)`. -/
theorem coe_nuBarCharacter_apply [IsCMField 𝒦] (n : ℕ) (ξ₀ : HeckeCharacter 𝒦₀)
    (a : IdeleClasses 𝒦) :
    (nuBarCharacter n ξ₀ a : ℂ) =
      ((ξ₀ (ideleClassNorm (K := 𝒦₀) (L := 𝒦) (ideleClassComplexConj a)) : ℂ))⁻¹ *
        ((((IdeleAbsoluteValue.ideleClass 𝒦 a : NNReal) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) :
          ℂ) := by
  rw [nuBarCharacter_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  congr 1
  have h := HeckeCharacter.normPower_ofReal_apply 𝒦 (((n : ℝ) - 1) / 2) a
  push_cast at h
  exact h

end Langlands.Global.Harris

namespace Langlands.GaloisRepresentation.Harris

open Langlands.Global
open NumberField (IsCMField)

variable {𝒦 : Type u} [Field 𝒦] [NumberField 𝒦] [IsCMField 𝒦]
variable {𝒦₀ : Type u₀} [Field 𝒦₀] [NumberField 𝒦₀] [Algebra 𝒦₀ 𝒦]
variable {L : Type uL} [Field L] [NumberField L]

/-- `ψ` is a `λ`-adic realization through `ι` of Harris's `ν̄(π)` built from
`n` and `ξ₀`: the `λ`-adic character written `ν̄(π)` in Harris 1999, (5.4) and
Theorem 5.7. Existence is not asserted. -/
def IsNuBarRealization (ι : L →+* ℂ) (lam : FinitePlace L) (n : ℕ)
    (ξ₀ : HeckeCharacter 𝒦₀) (ψ : LambdaAdicCharacter 𝒦 L lam) : Prop :=
  IsLambdaAdicRealization ι lam (Langlands.Global.Harris.nuBarCharacter n ξ₀) ψ

end Langlands.GaloisRepresentation.Harris
