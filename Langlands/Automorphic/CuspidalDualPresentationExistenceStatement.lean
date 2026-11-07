import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.CuspidalSpectralPresentation

/-! # Spectral presentation existence for a supplied cuspidal contragredient

A derived proposition for later proof, with independent input and output factor
universes and no unitarity hypothesis.
-/

noncomputable section

universe uF uP uQ

namespace Langlands.Automorphic

open Langlands.Global

/-- A supplied full-operator contragredient of a presented actual cusp object has
a spectral presentation in any independently specified factor universe. -/
def CuspidalDualPresentationExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T T' : CuspidalOperatorRealization F r),
    T'.realization.IsContragredientOf T.realization →
    CuspidalSpectralPresentation.{uF, uP} T →
    Nonempty (CuspidalSpectralPresentation.{uF, uQ} T')

end Langlands.Automorphic
