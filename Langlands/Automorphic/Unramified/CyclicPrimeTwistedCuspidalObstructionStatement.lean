import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Global.AdelicFunctoriality.Inclusion

/-! # The twisted cuspidal obstruction for a prime cyclic extension

The prime-degree finite-order specialization of Clozel–Rajan, Theorem 1,
using actual Galois pullback and the determinant twist on full cuspidal classes.
-/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization

/-- A character whose restriction is faithful on the cyclic norm quotient cannot
relate a cusp to its Galois conjugate by a determinant twist. -/
def CyclicPrimeTwistedCuspidalObstructionStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ χ : HeckeCharacter E, χ.HasFiniteOrder →
      HeckeCharacter.HasNormKernel E (χ.comp (ideleClassInclusion (K := F) (L := E))) →
      ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
        ¬ IsoClass.IsFiniteOrderDeterminantTwist χ T.isoClass
          (IsoClass.galoisConj σ T.isoClass)

/-- The twisted cuspidal obstruction over totally complex base fields. -/
def CyclicPrimeTwistedCuspidalObstructionTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ χ : HeckeCharacter E, χ.HasFiniteOrder →
      HeckeCharacter.HasNormKernel E (χ.comp (ideleClassInclusion (K := F) (L := E))) →
      ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
        ¬ IsoClass.IsFiniteOrderDeterminantTwist χ T.isoClass
          (IsoClass.galoisConj σ T.isoClass)

end Langlands.Automorphic.Unramified
