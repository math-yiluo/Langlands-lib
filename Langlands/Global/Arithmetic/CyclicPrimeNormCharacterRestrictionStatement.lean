import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.HeckeCharacterTransport

/-! # Norm-trivial characters at the bottom prime step of a cyclic tower -/

noncomputable section

universe uF uK uE

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open Langlands.Global.AdelicFunctoriality

/-- A character trivial on top norms is invariant under the bottom Galois group.
If it has the nontrivial prime order of the bottom extension, its restriction to
the base has that extension's norm image as kernel. -/
def CyclicPrimeNormCharacterRestrictionStatement : Prop :=
  ∀ (F : Type uF) (K : Type uK) (E : Type uE)
    [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [IsGalois F K] [IsGalois K E] [IsGalois F E]
    [IsCyclic (K ≃ₐ[F] K)] [IsCyclic (E ≃ₐ[K] E)] [IsCyclic (E ≃ₐ[F] E)],
    (Module.finrank F K).Prime →
    ∀ χ : HeckeCharacter K, χ.IsTrivialOnNorm E →
      (∀ τ : K ≃ₐ[F] K, HeckeCharacter.comap τ.toRingEquiv χ = χ) ∧
      (χ ^ Module.finrank F K = 1 → χ ≠ 1 →
        HasNormKernel K (χ.comp (ideleClassInclusion (K := F) (L := K))))

end Langlands.Global.HeckeCharacter
