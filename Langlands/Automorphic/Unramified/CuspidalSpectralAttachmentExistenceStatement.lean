import Langlands.Automorphic.CuspidalSpectralPresentation

/-! # Genuine cuspidal spectra in an independent factor universe -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified
open Langlands.Automorphic.CuspidalOperatorRealization

/-- Every actual cuspidal realization admits a genuine attached spectrum with
local factor carriers in the specified universe. -/
def CuspidalSpectralAttachmentExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    ∃ s : SpectralSystem (FinitePlace F) (r + 1),
      IsoClass.HasSpectralSystem.{uF, uV} T.isoClass s

end Langlands.Automorphic.Unramified
