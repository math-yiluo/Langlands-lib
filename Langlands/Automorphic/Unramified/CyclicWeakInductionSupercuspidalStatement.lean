import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Automorphic.SupercuspidalComponent

/-! # Supercuspidality at a nonsplit place of cyclic weak induction

The global consequence of Henniart--Herb (1995), Proposition 5.5, used in the
prime-degree branch of Harris (1998), Proposition 4.8. Its proof must also
identify global automorphic induction locally with the Henniart--Herb lift
and identify a supplied weak induction with that global induction.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization

/-- At a unique place above `v`, cyclic weak induction of a supercuspidal
component with distinct local Galois conjugates is supercuspidal. This is a
derived global input, not a standalone statement of the local lift theorem. -/
def CyclicWeakInductionSupercuspidalStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (r m : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E m)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      (P.localComponent w.1).IsSupercuspidal →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E →
        ∃ (U : CuspidalOperatorRealization E m)
          (Q : CuspidalSpectralPresentation.{uE, uW} U),
          T.isoClass.IsGaloisConjugate (σ ^ i) U.isoClass ∧
          (Q.localComponent w.1).IsSupercuspidal ∧
          (Q.localComponent w.1).isoClass ≠ (P.localComponent w.1).isoClass) →
      IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass →
      IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v

end Langlands.Automorphic.Unramified
