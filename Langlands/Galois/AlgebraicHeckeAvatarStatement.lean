import Langlands.Galois.HeckeAvatarCorrection
import Langlands.Galois.HeckeAvatarInverseLimit
import Langlands.Galois.HeckeCharacterRealization
import Langlands.Global.Arithmetic.HarrisSetup

/-! # A uniform family of adic avatars for an algebraic Hecke character -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped Valued

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

/-- A common coefficient field, conductor support and Frobenius values for a
family of actual adic characters. -/
def IsUniformHeckeAvatar (ι : L →+* ℂ) (χ : HeckeCharacter K)
    (S : Finset (FinitePlace K)) (a : FinitePlace K → Lˣ)
    (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam) : Prop :=
  (∀ v, v ∉ S ↔ χ.IsUnramifiedAt v) ∧
  ∀ v ∉ S,
    (∃ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) ∧
      (χ.finiteComponent v π : ℂ) = ι (a v : L)) ∧
    ∀ lam : FinitePlace L, residueCharacteristic v ≠ residueCharacteristic lam →
      (ψ lam).IsUnramifiedAt v ∧
        ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
          ((ψ lam).atFinitePlace v g : FiniteCompletion L lam) =
            NumberField.FinitePlace.embedding lam (a v : L)

/-- Each character of the uniform family realizes the Hecke character in
the published geometric Frobenius convention, using the same set `S`. -/
theorem IsUniformHeckeAvatar.isLambdaAdicRealization {ι : L →+* ℂ}
    {χ : HeckeCharacter K} {S : Finset (FinitePlace K)} {a : FinitePlace K → Lˣ}
    {ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam}
    (h : IsUniformHeckeAvatar ι χ S a ψ) (lam : FinitePlace L) :
    IsLambdaAdicRealization ι lam χ (ψ lam) := by
  refine ⟨S, fun v hv hchar => ?_⟩
  obtain ⟨hπ, hcoeff⟩ := h.2 v hv
  obtain ⟨hunr, hg⟩ := hcoeff lam hchar
  exact ⟨(h.1 v).mp hv, hunr, a v, hπ, geometricFrobeniusLift v,
    geometricFrobeniusLift_spec v, hg _ (geometricFrobeniusLift_spec v)⟩

/-- Uniform actual adic avatars for every algebraic CM Hecke character,
including those of nonzero weight. -/
def AlgebraicHeckeCharacterAvatarStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [NumberField.IsCMField K] (χ : HeckeCharacter K),
    Harris.IsAlgebraic χ →
    ∃ (L : Type uL) (hL : Field L),
      letI : Field L := hL
      ∃ (hnum : NumberField L),
        letI : NumberField L := hnum
        ∃ (ι : L →+* ℂ) (S : Finset (FinitePlace K)) (a : FinitePlace K → Lˣ)
          (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam),
          IsUniformHeckeAvatar ι χ S a ψ

/-- Assemble the uniform avatar from the common finite part, the idele
correction, the finite geometric lift, and the congruence limit. -/
def AlgebraicHeckeAvatarAssemblyStatement : Prop :=
  AlgebraicHeckeFinitePartStatement.{uK, uL} →
  HeckeAvatarIdeleCorrectionStatement.{uK, uL} →
  FiniteGeometricArtinLifting.{uK, uL} →
  HeckeAvatarInverseLimitStatement.{uK, uL} →
  AlgebraicHeckeCharacterAvatarStatement.{uK, uL}

end Langlands.GaloisRepresentation
