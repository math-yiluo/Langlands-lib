import Langlands.Automorphic.Unramified.CyclicPrimeTwistedCuspidalObstructionStatement

/-! # The central-character restriction on the twisted cuspidal rank

The remark after Clozel–Rajan, Theorem 1, before any use of the trace formula.
-/

universe uF uE

set_option autoImplicit false

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.Automorphic.CuspidalOperatorRealization

/-- If a full cuspidal class is conjugate to its determinant twist by a
finite-order character whose restriction has the norm kernel, the cyclic
extension degree divides the rank. A totally complex base needs no different
central-character argument. -/
def CyclicTwistedCuspidalRankDivisibilityStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient E)],
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ χ : HeckeCharacter E, χ.HasFiniteOrder →
      HeckeCharacter.HasNormKernel E (χ.comp (ideleClassInclusion (K := F) (L := E))) →
      ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
        IsoClass.IsFiniteOrderDeterminantTwist χ T.isoClass
          (IsoClass.galoisConj σ T.isoClass) →
        Module.finrank F E ∣ r + 1

end Langlands.TraceFormula
